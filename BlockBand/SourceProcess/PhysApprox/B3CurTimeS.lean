module

public import BlockBand.SourceProcess.PhysApprox.B3CurAlg
public import BlockBand.SourceProcess.ClosedReduce.StartAE
public import BlockBand.SourceProcess.ModelExist.ModeAlg

/-!
# The closed current at time `s`

Deterministic statements at the closing length `n_s = ⌊Ws⌋`, for one path `ω` with
`𝕊𝕊ᴴ = 1`, the cap `t_k ≤ h²` for `k ≥ K`, `t_k < 1` on retained modes and `h² < 1`. With
`T = T_far`, `F = physFw` (retained far eigenvectors), `D⁻ = diag((1-t_k)⁻¹)` and
`G₀ = 𝕊ᴴ ι_f S_ff F` (`retOut`):

* `farComplete_in`: `A_- + FFᴴ = 1` (far inputs); `farComplete_out`:
  `S_ff (g(T)² + F D⁻ Fᴴ) S_ffᴴ = 1` (far outputs), `g = pairWeight h`.
* `timeS_current_split`: `P' - P = A + F̂F̂ᴴ - (Π𝕊)ᴴ(Π𝕊) - G₀D⁻G₀ᴴ` (`F̂ = physF`).
* `closed_timeS_current`: for `|z| = 1`, `C(z)ᴴ(P' - P)C(z) = J_ret := F̂F̂ᴴ - G₀D⁻G₀ᴴ`.
* `pairing_mul_timeSFrame`: for an admissible frame (`IsTimeSFrame` clauses), `Π𝕊V_s = 0`.
* **`retCurrent_eq_frame`**: `J_ret = V_s 𝖣 V_sᴴ` (a trace argument: `J_ret V_s = V_s Λ`,
  `V_sᴴV_s = Δ`, and `tr J_ret² = tr Δ² = 2Σ_k t_k`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3Cur

open Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedSum
open BlockBand.SourceProcess.ClosedReduce BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess
open scoped ComplexOrder

variable {W : ℕ} {b E s h : ℝ} {K : ℕ} {ω : GrowthPath W}

/-!
## Notation
-/

/-- `g(T_far)`, `g = pairWeight h`: `Π = g(T_far) S_ffᴴ`. -/
def pw (b E s h : ℝ) (W : ℕ) (ω : GrowthPath W) : Matrix (Fin W) (Fin W) ℂ :=
  cfc (pairWeight h) (farTransmission b E W (closeLen s W) ω)

/-- `D⁻ = diag((1 - t_k)⁻¹)`. -/
def dInv (b E s : ℝ) (K W : ℕ) (ω : GrowthPath W) : Matrix (Fin K) (Fin K) ℂ :=
  diagonal fun k => (((1 - physTseq b E s W ω k.val)⁻¹ : ℝ) : ℂ)

/-- `G₀ = 𝕊ᴴ ι_f S_ff F`: the inputs feeding the retained far outputs. -/
def retOut (b E s h : ℝ) (K W : ℕ) (ω : GrowthPath W) : Matrix (Fin 2 × Fin W) (Fin K) ℂ :=
  (scatteringMatrix b E W (closeLen s W) ω)ᴴ * farInj W * farReflection b E W (closeLen s W) ω *
    physFw b E s h K W ω

/-- **The retained current** `J_ret = F̂F̂ᴴ - G₀D⁻G₀ᴴ`. -/
def retCurrent (b E s h : ℝ) (K W : ℕ) (ω : GrowthPath W) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  physF b E s h K W ω * (physF b E s h K W ω)ᴴ -
    retOut b E s h K W ω * dInv b E s K W ω * (retOut b E s h K W ω)ᴴ

/-- The signature `𝖣` on the current columns. -/
def sig2 (K : ℕ) : Matrix (Fin K × Fin 2) (Fin K × Fin 2) ℂ :=
  diagonal fun c => if c.2 = 0 then 1 else -1

/-!
## Completeness of the far eigenvectors on the cap
-/

theorem eq_one_of_physFarVec {M : Matrix (Fin W) (Fin W) ℂ}
    (hM : ∀ k, k < Fintype.card (Fin W) →
      M *ᵥ physFarVec b E s W ω k = physFarVec b E s W ω k) : M = 1 := by
  set hT := isHermitian_farTransmission b E W (closeLen s W) ω
  set U : Matrix (Fin W) (Fin W) ℂ := (hT.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hMU : M * U = U := by
    ext i j
    set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin W)))
    have hk := (e.symm j).isLt
    have hv : physFarVec b E s W ω (e.symm j).val = ⇑(hT.eigenvectorBasis j) := by
      simp only [physFarVec, hk, ↓reduceDIte, sortIdx, Fin.eta]
      rw [show (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin W)))) (e.symm j) = j
        from e.apply_symm_apply j]
    have := congrFun (hM _ hk) i
    rw [hv] at this
    simp only [mul_apply, U, IsHermitian.eigenvectorUnitary_apply]
    simpa [mulVec, dotProduct] using this
  calc M = M * (U * star U) := by rw [hUU', Matrix.mul_one]
    _ = U * star U := by rw [← Matrix.mul_assoc, hMU]
    _ = 1 := hUU'

theorem physFw_conj_mulVec {j : ℕ} (hj : j < Fintype.card (Fin W)) :
    (physFw b E s h K W ω)ᴴ *ᵥ physFarVec b E s W ω j =
      fun k => if k.val = j ∧ h ^ 2 < physTseq b E s W ω k.val then 1 else 0 := by
  funext k
  by_cases hk : h ^ 2 < physTseq b E s W ω k.val
  · have e := physFarVec_orthonormal (b := b) (E := E) (s := s) (ω := ω) (retained_lt_card hk) hj
    simp only [mulVec, dotProduct, conjTranspose_apply, physFw, of_apply, hk, ↓reduceIte,
      and_true] at e ⊢
    rw [← e]
    rfl
  · simp [mulVec, dotProduct, physFw, hk]

theorem physFw_diag_mulVec (d : Fin K → ℂ) {j : ℕ} (hj : j < Fintype.card (Fin W)) :
    (physFw b E s h K W ω * diagonal d * (physFw b E s h K W ω)ᴴ) *ᵥ physFarVec b E s W ω j =
      (∑ k : Fin K, if k.val = j ∧ h ^ 2 < physTseq b E s W ω k.val then d k else 0) •
        physFarVec b E s W ω j := by
  rw [← mulVec_mulVec, physFw_conj_mulVec hj, ← mulVec_mulVec]
  rw [show (diagonal d *ᵥ fun k : Fin K =>
      if k.val = j ∧ h ^ 2 < physTseq b E s W ω k.val then (1 : ℂ) else 0) =
      fun k => d k * if k.val = j ∧ h ^ 2 < physTseq b E s W ω k.val then (1 : ℂ) else 0 from
    funext fun k => mulVec_diagonal _ _ k]
  funext a
  simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k.val = j ∧ h ^ 2 < physTseq b E s W ω k.val
  · rcases hk with ⟨rfl, hk2⟩
    simp [physFw, hk2, mul_comm]
  · simp [hk]

theorem lt_of_ret (hcap : ∀ k, K ≤ k → physTseq b E s W ω k ≤ h ^ 2) {j : ℕ}
    (hj : h ^ 2 < physTseq b E s W ω j) : j < K := by
  by_contra hc
  exact absurd (hcap j (not_lt.1 hc)) (not_le.2 hj)

theorem sum_ret_eq (hcap : ∀ k, K ≤ k → physTseq b E s W ω k ≤ h ^ 2) (d : Fin K → ℂ) (j : ℕ) :
    (∑ k : Fin K, if k.val = j ∧ h ^ 2 < physTseq b E s W ω k.val then d k else 0) =
      if hj : h ^ 2 < physTseq b E s W ω j then d ⟨j, lt_of_ret hcap hj⟩ else 0 := by
  split_ifs with hj
  · rw [Finset.sum_eq_single ⟨j, lt_of_ret hcap hj⟩]
    · simp [hj]
    · intro k _ hk
      have : k.val ≠ j := fun e => hk (Fin.ext e)
      simp [this]
    · simp
  · refine Finset.sum_eq_zero fun k _ => ?_
    have : ¬ (k.val = j ∧ h ^ 2 < physTseq b E s W ω k.val) := by
      rintro ⟨rfl, h2⟩
      exact hj h2
    simp only [this, ↓reduceIte]

/-- **Far inputs are complete on the cap**: `A_- + FFᴴ = 1`. -/
theorem farComplete_in (hcap : ∀ k, K ≤ k → physTseq b E s W ω k ≤ h ^ 2) :
    omittedProj b E h W (closeLen s W) ω + physFw b E s h K W ω * (physFw b E s h K W ω)ᴴ =
      1 := by
  apply eq_one_of_physFarVec (b := b) (E := E) (s := s) (ω := ω)
  intro j hj
  have hA := cfc_mulVec_of_eigen (isHermitian_farTransmission b E W (closeLen s W) ω)
    (omitIndicator h) (farTransmission_mulVec_physFarVec (b := b) (E := E) (s := s) (ω := ω) j)
  have hF := physFw_diag_mulVec (b := b) (E := E) (s := s) (h := h) (K := K) (ω := ω)
    (fun _ => 1) hj
  rw [diagonal_one, Matrix.mul_one, sum_ret_eq hcap] at hF
  rw [add_mulVec, hF]
  unfold omittedProj
  rw [hA, ← add_smul]
  by_cases ht : h ^ 2 < physTseq b E s W ω j
  · simp [omitIndicator, ht, not_le.2 ht]
  · simp [omitIndicator, ht, not_lt.1 ht]

/-- **Far outputs are complete on the cap**: `S_ff (g(T)² + F D⁻ Fᴴ) S_ffᴴ = 1`. -/
theorem farComplete_out (hcap : ∀ k, K ≤ k → physTseq b E s W ω k ≤ h ^ 2)
    (hlt : ∀ k : Fin K, h ^ 2 < physTseq b E s W ω k.val → physTseq b E s W ω k.val < 1)
    (hh : h ^ 2 < 1) :
    farReflection b E W (closeLen s W) ω *
      (pw b E s h W ω * pw b E s h W ω + physFw b E s h K W ω * dInv b E s K W ω *
        (physFw b E s h K W ω)ᴴ) * (farReflection b E W (closeLen s W) ω)ᴴ = 1 := by
  set R := farReflection b E W (closeLen s W) ω
  set X := pw b E s h W ω * pw b E s h W ω + physFw b E s h K W ω * dInv b E s K W ω *
    (physFw b E s h K W ω)ᴴ
  have hX : X * (Rᴴ * R) = 1 := by
    apply eq_one_of_physFarVec (b := b) (E := E) (s := s) (ω := ω)
    intro j hj
    have hTv := farTransmission_mulVec_physFarVec (b := b) (E := E) (s := s) (ω := ω) j
    have hRR : (Rᴴ * R) *ᵥ physFarVec b E s W ω j = ((1 - physTseq b E s W ω j : ℝ) : ℂ) •
        physFarVec b E s W ω j := by
      have e : Rᴴ * R = 1 - farTransmission b E W (closeLen s W) ω := by
        simp only [farTransmission, R, sub_sub_cancel]
      rw [e, sub_mulVec, one_mulVec, hTv, Complex.ofReal_sub, Complex.ofReal_one, sub_smul,
        one_smul]
    have hg := cfc_mulVec_of_eigen (isHermitian_farTransmission b E W (closeLen s W) ω)
      (pairWeight h) hTv
    have hF := physFw_diag_mulVec (b := b) (E := E) (s := s) (h := h) (K := K) (ω := ω)
      (fun k => (((1 - physTseq b E s W ω k.val)⁻¹ : ℝ) : ℂ)) hj
    rw [sum_ret_eq hcap] at hF
    have hXv : X *ᵥ physFarVec b E s W ω j =
        (((1 - physTseq b E s W ω j)⁻¹ : ℝ) : ℂ) • physFarVec b E s W ω j := by
      simp only [X, add_mulVec]
      rw [← mulVec_mulVec, dInv, hF]
      unfold pw
      rw [hg, mulVec_smul, hg, smul_smul, ← add_smul]
      congr 1
      by_cases ht : h ^ 2 < physTseq b E s W ω j
      · have hp : pairWeight h (physTseq b E s W ω j) = 0 := by
          simp [pairWeight, not_le.2 ht]
        simp only [ht, ↓reduceDIte, hp, Complex.ofReal_zero, mul_zero, zero_add]
      · have hpos : 0 < 1 - physTseq b E s W ω j := by linarith [not_lt.1 ht]
        have hsq := Real.mul_self_sqrt hpos.le
        have hs : Real.sqrt (1 - physTseq b E s W ω j) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
        have hp : pairWeight h (physTseq b E s W ω j) =
            (Real.sqrt (1 - physTseq b E s W ω j))⁻¹ := by
          simp [pairWeight, not_lt.1 ht]
        simp only [ht, ↓reduceDIte, hp, add_zero]
        rw [← Complex.ofReal_mul]
        congr 1
        rw [← mul_inv, hsq]
    have hne : 1 - physTseq b E s W ω j ≠ 0 := by
      by_cases ht : h ^ 2 < physTseq b E s W ω j
      · have := hlt ⟨j, lt_of_ret hcap ht⟩ ht
        exact (sub_pos.2 this).ne'
      · linarith [not_lt.1 ht]
    rw [← mulVec_mulVec, hRR, mulVec_smul, hXv, smul_smul, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hne, Complex.ofReal_one, one_smul]
  have hXR : (X * Rᴴ) * R = 1 := by rw [Matrix.mul_assoc]; exact hX
  have h2 : R * (X * Rᴴ) = 1 := mul_eq_one_comm.mp hXR
  rw [Matrix.mul_assoc]; exact h2

/-!
## The time-`s` current splits into omitted and retained parts
-/

theorem farInj_conj_mul_mul_farInj (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    (farInj W)ᴴ * S * farInj W = portBlock S 1 1 := by
  ext a c
  simp only [mul_apply, conjTranspose_apply, farInj, of_apply, portBlock]
  rw [Finset.sum_eq_single (1, c) (fun y _ hy => by simp [hy]) (by simp)]
  rw [Finset.sum_eq_single (1, a) (fun y _ hy => by simp [hy]) (by simp)]
  simp

theorem farInj_conj_mul_farInj_mul {κ : Type*} (Y : Matrix (Fin W) κ ℂ) :
    (farInj W)ᴴ * (farInj W * Y) = Y := by
  rw [← Matrix.mul_assoc, farInj_conj_mul_self, Matrix.one_mul]

theorem pw_conjTranspose : (pw b E s h W ω)ᴴ = pw b E s h W ω := cfc_conjTranspose _ _

/-- **The time-`s` current** `P' - P = A + F̂F̂ᴴ - (Π𝕊)ᴴ(Π𝕊) - G₀D⁻G₀ᴴ` on the cap. -/
theorem timeS_current_split
    (hS : scatteringMatrix b E W (closeLen s W) ω *
      (scatteringMatrix b E W (closeLen s W) ω)ᴴ = 1)
    (hcap : ∀ k, K ≤ k → physTseq b E s W ω k ≤ h ^ 2)
    (hlt : ∀ k : Fin K, h ^ 2 < physTseq b E s W ω k.val → physTseq b E s W ω k.val < 1)
    (hh : h ^ 2 < 1) :
    physOutProj b E s W ω - nearPortProj W =
      farEmbed (omittedProj b E h W (closeLen s W) ω) +
        physF b E s h K W ω * (physF b E s h K W ω)ᴴ -
        (farEmbed (closingPairing b E h W (closeLen s W) ω) *
          scatteringMatrix b E W (closeLen s W) ω)ᴴ *
          (farEmbed (closingPairing b E h W (closeLen s W) ω) *
            scatteringMatrix b E W (closeLen s W) ω) -
        retOut b E s h K W ω * dInv b E s K W ω * (retOut b E s h K W ω)ᴴ := by
  set S := scatteringMatrix b E W (closeLen s W) ω
  set P := nearPortProj W
  have hS' : Sᴴ * S = 1 := mul_eq_one_comm.mp hS
  have e1 : physOutProj b E s W ω - P = (1 - P) - Sᴴ * (1 - P) * S := by
    simp only [physOutProj, S, P, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one] at hS' ⊢
    rw [hS']; abel
  have e2 : 1 - P = farEmbed (omittedProj b E h W (closeLen s W) ω) +
      physF b E s h K W ω * (physF b E s h K W ω)ᴴ := by
    calc 1 - P = farInj W * (omittedProj b E h W (closeLen s W) ω +
          physFw b E s h K W ω * (physFw b E s h K W ω)ᴴ) * (farInj W)ᴴ := by
          rw [farComplete_in hcap, Matrix.mul_one, one_sub_nearPortProj]
      _ = _ := by
          rw [farEmbed_eq_farInj, physF]
          simp only [Matrix.mul_add, Matrix.add_mul, conjTranspose_mul, Matrix.mul_assoc]
  have e3 : Sᴴ * (1 - P) * S =
      (farEmbed (closingPairing b E h W (closeLen s W) ω) * S)ᴴ *
          (farEmbed (closingPairing b E h W (closeLen s W) ω) * S) +
        retOut b E s h K W ω * dInv b E s K W ω * (retOut b E s h K W ω)ᴴ := by
    calc Sᴴ * (1 - P) * S = Sᴴ * farInj W * (farReflection b E W (closeLen s W) ω *
          (pw b E s h W ω * pw b E s h W ω + physFw b E s h K W ω * dInv b E s K W ω *
            (physFw b E s h K W ω)ᴴ) * (farReflection b E W (closeLen s W) ω)ᴴ) *
          (farInj W)ᴴ * S := by
          rw [farComplete_out hcap hlt hh, Matrix.mul_one, one_sub_nearPortProj]
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [farEmbed_eq_farInj, retOut]
          change _ = (farInj W * (pw b E s h W ω * (farReflection b E W (closeLen s W) ω)ᴴ) *
            (farInj W)ᴴ * S)ᴴ * (farInj W * (pw b E s h W ω *
              (farReflection b E W (closeLen s W) ω)ᴴ) * (farInj W)ᴴ * S) + _
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, pw_conjTranspose,
            Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, farInj_conj_mul_farInj_mul]
          rfl
  rw [e1, e3, e2]; abel

/-- `A` kills the retained far frame `F̂`. -/
theorem omitted_mul_physF :
    farEmbed (omittedProj b E h W (closeLen s W) ω) * physF b E s h K W ω = 0 := by
  rw [physF, ← Matrix.mul_assoc, farEmbed_mul_farInj, Matrix.mul_assoc, omittedProj_mul_physFw,
    Matrix.mul_zero]

/-- `A` kills `G₀`. -/
theorem omitted_mul_retOut :
    farEmbed (omittedProj b E h W (closeLen s W) ω) * retOut b E s h K W ω = 0 := by
  set S := scatteringMatrix b E W (closeLen s W) ω
  set R := farReflection b E W (closeLen s W) ω
  have hR : (farInj W)ᴴ * Sᴴ * farInj W = Rᴴ := by
    rw [show R = (farInj W)ᴴ * S * farInj W from (farInj_conj_mul_mul_farInj S).symm]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hRR : Rᴴ * R = 1 - farTransmission b E W (closeLen s W) ω := by
    simp only [farTransmission, R, sub_sub_cancel]
  calc farEmbed (omittedProj b E h W (closeLen s W) ω) * retOut b E s h K W ω =
      farInj W * (omittedProj b E h W (closeLen s W) ω * (Rᴴ * R) * physFw b E s h K W ω) := by
        rw [farEmbed_eq_farInj, retOut, ← hR]
        simp only [Matrix.mul_assoc]
        rfl
    _ = 0 := by
        rw [hRR, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.mul_assoc,
          farTransmission_mul_physFw, ← Matrix.mul_assoc, omittedProj_mul_physFw,
          Matrix.zero_mul, sub_self, Matrix.mul_zero]

/-- **Closing at time `s` hypotheses the retained current**: `C(z)ᴴ(P' - P)C(z) = J_ret`,
`|z| = 1`. -/
theorem closed_timeS_current
    (hS : scatteringMatrix b E W (closeLen s W) ω *
      (scatteringMatrix b E W (closeLen s W) ω)ᴴ = 1)
    (hcap : ∀ k, K ≤ k → physTseq b E s W ω k ≤ h ^ 2)
    (hlt : ∀ k : Fin K, h ^ 2 < physTseq b E s W ω k.val → physTseq b E s W ω k.val < 1)
    (hh : h ^ 2 < 1) {z : ℂ} (hz : ‖z‖ = 1)
    (hU : IsUnit (1 - z • closingN (scatteringMatrix b E W (closeLen s W) ω)
      (farEmbed (omittedProj b E h W (closeLen s W) ω))
      (farEmbed (closingPairing b E h W (closeLen s W) ω))).det) :
    (physClosingMapAt b E s h W (closeLen s W) ω z)ᴴ * (physOutProj b E s W ω - nearPortProj W) *
      physClosingMapAt b E s h W (closeLen s W) ω z = retCurrent b E s h K W ω := by
  set S := scatteringMatrix b E W (closeLen s W) ω
  set A := farEmbed (omittedProj b E h W (closeLen s W) ω)
  set Pi := farEmbed (closingPairing b E h W (closeLen s W) ω)
  set C := physClosingMapAt b E s h W (closeLen s W) ω z
  have hAH : Aᴴ = A := by rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
  have hAA : A * A = A := by rw [farEmbed_mul, omittedProj_mul_self]
  have hAPi : A * Pi = Pi := by rw [farEmbed_mul, omittedProj_mul_closingPairing]
  have hC : C = closingMap S A Pi z := rfl
  have h0 : Cᴴ * (A - (Pi * S)ᴴ * (Pi * S)) * C = 0 := by
    rw [hC]; exact closed_omitted_current hAH hAA hAPi hU hz
  have hF : Cᴴ * physF b E s h K W ω = physF b E s h K W ω := by
    rw [hC]; exact closingMap_conj_fix hAH hAPi omitted_mul_physF
  have hG : Cᴴ * retOut b E s h K W ω = retOut b E s h K W ω := by
    rw [hC]; exact closingMap_conj_fix hAH hAPi omitted_mul_retOut
  have hsw : ∀ {κ : Type} [Fintype κ] (X : Matrix (Fin 2 × Fin W) κ ℂ) (M : Matrix κ κ ℂ),
      Cᴴ * X = X → Cᴴ * (X * M * Xᴴ) * C = X * M * Xᴴ := by
    intro κ _ X M hX
    have hX' : Xᴴ * C = Xᴴ := by
      have := congrArg conjTranspose hX
      rwa [conjTranspose_mul, conjTranspose_conjTranspose] at this
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hX, Matrix.mul_assoc, hX']
  have hFF := hsw (physF b E s h K W ω) 1 hF
  have hGG := hsw (retOut b E s h K W ω) (dInv b E s K W ω) hG
  rw [Matrix.mul_one] at hFF
  rw [timeS_current_split hS hcap hlt hh]
  change Cᴴ * (A + physF b E s h K W ω * (physF b E s h K W ω)ᴴ - (Pi * S)ᴴ * (Pi * S) -
    retOut b E s h K W ω * dInv b E s K W ω * (retOut b E s h K W ω)ᴴ) * C = _
  have e : A + physF b E s h K W ω * (physF b E s h K W ω)ᴴ - (Pi * S)ᴴ * (Pi * S) -
      retOut b E s h K W ω * dInv b E s K W ω * (retOut b E s h K W ω)ᴴ =
      (A - (Pi * S)ᴴ * (Pi * S)) + physF b E s h K W ω * (physF b E s h K W ω)ᴴ -
        retOut b E s h K W ω * dInv b E s K W ω * (retOut b E s h K W ω)ᴴ := by abel
  rw [e, Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul, Matrix.add_mul, h0, hFF, hGG, zero_add,
    retCurrent]

/-!
## Admissible frames: `Π𝕊V_s = 0`
-/

theorem conj_portBlock_far {S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hS : S * Sᴴ = 1) :
    (portBlock Sᴴ 0 1)ᴴ * portBlock Sᴴ 0 1 = 1 - portBlock S 1 1 * (portBlock S 1 1)ᴴ := by
  ext a c
  have h := congrFun (congrFun hS (1, a)) (1, c)
  simp only [mul_apply, conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    one_apply, Prod.mk.injEq, true_and] at h
  simp only [Matrix.sub_apply, mul_apply, conjTranspose_apply, portBlock, of_apply, one_apply,
    star_star]
  rw [← h]; ring

/-- **The paired omitted outputs of an admissible frame vanish**: `Π𝕊V_s = 0`. -/
theorem pairing_mul_timeSFrame (Vs : Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (hS : scatteringMatrix b E W (closeLen s W) ω *
      (scatteringMatrix b E W (closeLen s W) ω)ᴴ = 1)
    (hG : gramPair (nearPortProj W) Vs =
      curGramOf (initialGram K (Fin 0) (physTseq b E s W ω) h))
    (hE : ∀ x k, ((physOutProj b E s W ω - nearPortProj W) * Vs) x k =
      modeEig (physTseq b E s W ω k.1.val) k.2 * Vs x k) :
    farEmbed (closingPairing b E h W (closeLen s W) ω) * scatteringMatrix b E W (closeLen s W) ω *
      Vs = 0 := by
  set S := scatteringMatrix b E W (closeLen s W) ω
  set P := nearPortProj W
  set R := farReflection b E W (closeLen s W) ω
  have hS' : Sᴴ * S = 1 := mul_eq_one_comm.mp hS
  ext x k
  set v : Fin 2 × Fin W → ℂ := fun y => Vs y k
  set t := physTseq b E s W ω k.1.val
  have hcol : (farEmbed (closingPairing b E h W (closeLen s W) ω) * S * Vs) x k =
      ((farEmbed (closingPairing b E h W (closeLen s W) ω) * S) *ᵥ v) x := by
    simp [mul_apply, mulVec, dotProduct, v]
  rw [hcol, Matrix.zero_apply]
  by_cases ht : h ^ 2 < t
  · have hv : (Sᴴ * P * S - P) *ᵥ v = modeEig t k.2 • v := by
      funext y
      have := hE y k
      simp only [mul_apply] at this
      simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, v]
      exact this
    have ht0 : 0 ≤ t := (sq_nonneg h).trans ht.le
    have hcc : (-modeEig t k.2) * (-modeEig t k.2) = (t : ℂ) := by
      have : (Real.sqrt t : ℂ) * (Real.sqrt t : ℂ) = (t : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt ht0]
      unfold modeEig; split_ifs <;> simp [this]
    have key : (Sᴴᴴ * P * Sᴴ - P) * S = -(S * (Sᴴ * P * S - P)) := by
      rw [conjTranspose_conjTranspose]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hS', Matrix.mul_one]
      rw [← Matrix.mul_assoc S Sᴴ, hS, Matrix.one_mul]; abel
    have hv' : (Sᴴᴴ * P * Sᴴ - P) *ᵥ (S *ᵥ v) = (-modeEig t k.2) • (S *ᵥ v) := by
      rw [mulVec_mulVec, key, neg_mulVec, ← mulVec_mulVec, hv, mulVec_smul, neg_smul]
    have hSS : Sᴴ * Sᴴᴴ = 1 := by rw [conjTranspose_conjTranspose]; exact hS'
    have hf := farTrans_mulVec_far hSS hv'
    rw [hcc, conj_portBlock_far hS] at hf
    set w := (farInj W)ᴴ *ᵥ (S *ᵥ v)
    have hT : farTransmission b E W (closeLen s W) ω *ᵥ (Rᴴ *ᵥ w) = (t : ℂ) • (Rᴴ *ᵥ w) := by
      have e : farTransmission b E W (closeLen s W) ω * Rᴴ = Rᴴ * (1 - R * Rᴴ) := by
        simp only [farTransmission, R, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
          Matrix.mul_one, Matrix.mul_assoc]
      rw [mulVec_mulVec, e, ← mulVec_mulVec]
      change Rᴴ *ᵥ ((1 - portBlock S 1 1 * (portBlock S 1 1)ᴴ) *ᵥ w) = _
      rw [hf, mulVec_smul]
    have hg := cfc_mulVec_of_eigen (isHermitian_farTransmission b E W (closeLen s W) ω)
      (pairWeight h) hT
    have hz : pairWeight h t = 0 := by simp [pairWeight, not_le.2 ht]
    rw [hz, Complex.ofReal_zero, zero_smul] at hg
    have e2 : farEmbed (closingPairing b E h W (closeLen s W) ω) * S =
        farInj W * (pw b E s h W ω * (Rᴴ * ((farInj W)ᴴ * S))) := by
      rw [farEmbed_eq_farInj]
      simp only [closingPairing, pw, R, Matrix.mul_assoc]
    rw [e2, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
    change (farInj W *ᵥ (pw b E s h W ω *ᵥ (Rᴴ *ᵥ w))) x = 0
    unfold pw
    rw [hg, mulVec_zero, Pi.zero_apply]
  · have hk := congrArg (fun G => G.1 k k) hG
    have h0 : star v ⬝ᵥ v = 0 := by
      simp only [gramPair, sourceGram, curGramOf, initialGram, initialFrame, mul_apply,
        conjTranspose_apply, submatrix_apply] at hk
      simp only [dotProduct, Pi.star_apply, v]
      rw [hk]
      refine Finset.sum_eq_zero fun y _ => ?_
      have : ¬ (y.1 = k.1 ∧ h ^ 2 < physTseq b E s W ω k.1.val) := fun hy => ht hy.2
      simp [this]
    rw [dotProduct_star_self_eq_zero.1 h0, mulVec_zero, Pi.zero_apply]

/-!
## The Gram matrix of an admissible frame
-/

theorem ev_orth {t : ℝ} (h1 : t ≤ 1) (σ σ' : Fin 2) :
    ∑ a, ModelExist.ev t σ a * ModelExist.ev t σ' a = if σ = σ' then 1 else 0 := by
  have hs0 := Real.sqrt_nonneg t
  have hs1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.2 h1
  have ha : Real.sqrt (1 - Real.sqrt t) * Real.sqrt (1 - Real.sqrt t) = 1 - Real.sqrt t :=
    Real.mul_self_sqrt (by linarith)
  have hb : Real.sqrt (1 + Real.sqrt t) * Real.sqrt (1 + Real.sqrt t) = 1 + Real.sqrt t :=
    Real.mul_self_sqrt (by linarith)
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hd : ∀ x y : ℝ, x / Real.sqrt 2 * (y / Real.sqrt 2) = x * y / 2 := by
    intro x y; rw [div_mul_div_comm, h2]
  have hd' : ∀ x y : ℝ, x / Real.sqrt 2 * -(y / Real.sqrt 2) = -(x * y / 2) := by
    intro x y; rw [mul_neg, hd]
  have hd'' : ∀ x y : ℝ, -(x / Real.sqrt 2) * -(y / Real.sqrt 2) = x * y / 2 := by
    intro x y; rw [neg_mul_neg, hd]
  have hd3 : ∀ x y : ℝ, -(x / Real.sqrt 2) * (y / Real.sqrt 2) = -(x * y / 2) := by
    intro x y; rw [neg_mul, hd]
  fin_cases σ <;> fin_cases σ' <;>
    simp only [Fin.sum_univ_two, ModelExist.ev, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      ↓reduceIte, one_ne_zero, zero_ne_one, hd, hd', hd'', hd3, ha, hb] <;> ring

theorem curGram_initialGram_fst (t : ℕ → ℝ) (h : ℝ)
    (ht : ∀ k : Fin K, h ^ 2 < t k.val → t k.val ≤ 1) :
    (curGramOf (initialGram K (Fin 0) t h)).1 =
      diagonal fun c : Fin K × Fin 2 =>
        if h ^ 2 < t c.1.val then ((Real.sqrt (t c.1.val) : ℝ) : ℂ) else 0 := by
  ext ⟨k, σ⟩ ⟨l, σ'⟩
  simp only [curGramOf, initialGram, gramPair, sourceGram, submatrix_apply, mul_apply,
    conjTranspose_apply, initialFrame, diagonal_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single k (fun x _ hx => by simp [hx]) (by simp)]
  by_cases hr : h ^ 2 < t k.val
  · have h0 : 0 ≤ t k.val := (sq_nonneg h).trans hr.le
    by_cases hkl : k = l
    · subst hkl
      have e : ∀ x2 : Fin 2, star (((t k.val ^ (1 / 4 : ℝ) : ℝ) : ℂ) * modeVector (t k.val) σ x2) *
          (((t k.val ^ (1 / 4 : ℝ) : ℝ) : ℂ) * modeVector (t k.val) σ' x2) =
          ((t k.val ^ (1 / 4 : ℝ) * t k.val ^ (1 / 4 : ℝ) *
            (ModelExist.ev (t k.val) σ x2 * ModelExist.ev (t k.val) σ' x2) : ℝ) : ℂ) := by
        intro x2
        rw [ModelExist.modeVector_eq, ModelExist.modeVector_eq, ← Complex.ofReal_mul,
          ← Complex.ofReal_mul, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
        congr 1; ring
      simp only [hr, and_self, ↓reduceIte, e]
      rw [← Complex.ofReal_sum, ← Finset.mul_sum, ev_orth (ht k hr),
        ModelExist.rpow_quarter_mul h0]
      by_cases hσ : σ = σ'
      · subst hσ; simp
      · have : ¬ ((k, σ) = (k, σ')) := fun e => hσ (Prod.ext_iff.1 e).2
        simp [hσ, this]
    · have : ¬ ((k, σ) = (l, σ')) := fun e => hkl (Prod.ext_iff.1 e).1
      simp [hkl, this]
  · have : ¬ ((k, σ) = (l, σ')) ∨ ¬ h ^ 2 < t k.val := Or.inr hr
    by_cases hkl : (k, σ) = (l, σ')
    · simp [hr, hkl]
    · simp [hr, hkl]

/-!
## The retained current is the frame current (trace argument)
-/

theorem trace_sandwich {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (A : Matrix ι κ ℂ) (M : Matrix κ κ ℂ) (B : Matrix ι μ ℂ) (N : Matrix μ μ ℂ) :
    trace (A * M * Aᴴ * (B * N * Bᴴ)) = trace (M * (Aᴴ * B) * N * (Bᴴ * A)) := by
  rw [show A * M * Aᴴ * (B * N * Bᴴ) = A * (M * (Aᴴ * B) * N * Bᴴ) by
    simp only [Matrix.mul_assoc], trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- **A trace criterion for `J = V𝖣Vᴴ`**: `J` Hermitian, `JV = VΛ`, `VᴴV = Δ` and
`tr J² - 2 tr(Λ𝖣Δ) + tr(𝖣Δ𝖣Δ) = 0`. -/
theorem eq_frame_of_trace {ι κ : Type*} [Fintype ι] [Fintype κ] {J : Matrix ι ι ℂ}
    {V : Matrix ι κ ℂ} {D L Δ : Matrix κ κ ℂ} (hJH : Jᴴ = J) (hDH : Dᴴ = D)
    (hJV : J * V = V * L) (hVV : Vᴴ * V = Δ)
    (htr : trace (J * J) - 2 * trace (L * D * Δ) + trace (D * Δ * D * Δ) = 0) :
    J = V * D * Vᴴ := by
  have hRH : (J - V * D * Vᴴ)ᴴ = J - V * D * Vᴴ := by
    rw [conjTranspose_sub, hJH]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hDH, Matrix.mul_assoc]
  have hJQ : trace (J * (V * D * Vᴴ)) = trace (L * D * Δ) := by
    rw [show J * (V * D * Vᴴ) = V * (L * D * Vᴴ) by simp only [← Matrix.mul_assoc, hJV],
      trace_mul_comm, ← hVV]
    simp only [Matrix.mul_assoc]
  have hQJ : trace (V * D * Vᴴ * J) = trace (J * (V * D * Vᴴ)) := trace_mul_comm _ _
  have hQQ : trace (V * D * Vᴴ * (V * D * Vᴴ)) = trace (D * Δ * D * Δ) := by
    rw [trace_sandwich, hVV]
  have h0 : trace ((J - V * D * Vᴴ)ᴴ * (J - V * D * Vᴴ)) = 0 := by
    rw [hRH, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, trace_sub, trace_sub, trace_sub,
      hQJ, hJQ, hQQ, ← htr]
    ring
  exact sub_eq_zero.1 (trace_conjTranspose_mul_self_eq_zero_iff.1 h0)

/-- `F̂ᴴG₀ = G₀ᴴF̂ = G₀ᴴG₀ = diag(m_k(1 - t_k))`. -/
def cDiag (b E s h : ℝ) (K W : ℕ) (ω : GrowthPath W) : Matrix (Fin K) (Fin K) ℂ :=
  diagonal fun k => retainMask K (physTseq b E s W ω) h k * (1 - (physTseq b E s W ω k.val : ℂ))

theorem farFw_conj_mul_self_sub :
    (physFw b E s h K W ω)ᴴ * ((farReflection b E W (closeLen s W) ω)ᴴ *
      (farReflection b E W (closeLen s W) ω * physFw b E s h K W ω)) = cDiag b E s h K W ω := by
  have hRR : (farReflection b E W (closeLen s W) ω)ᴴ * farReflection b E W (closeLen s W) ω =
      1 - farTransmission b E W (closeLen s W) ω := by
    simp only [farTransmission, sub_sub_cancel]
  rw [← Matrix.mul_assoc (farReflection b E W (closeLen s W) ω)ᴴ, hRR, Matrix.sub_mul,
    Matrix.one_mul, farTransmission_mul_physFw, Matrix.mul_sub, ← Matrix.mul_assoc,
    physFw_conj_mul_self]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [cDiag, maskDiag, tDiag, mul_sub]
  · simp [cDiag, maskDiag, tDiag, hij]

theorem physF_conj_mul_retOut :
    (physF b E s h K W ω)ᴴ * retOut b E s h K W ω = cDiag b E s h K W ω := by
  rw [physF, retOut, ← farFw_conj_mul_self_sub]
  have hR : (farInj W)ᴴ * (scatteringMatrix b E W (closeLen s W) ω)ᴴ * farInj W =
      (farReflection b E W (closeLen s W) ω)ᴴ := by
    rw [show farReflection b E W (closeLen s W) ω = (farInj W)ᴴ *
      scatteringMatrix b E W (closeLen s W) ω * farInj W from
      (farInj_conj_mul_mul_farInj _).symm]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← hR]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

theorem cDiag_conjTranspose : (cDiag b E s h K W ω)ᴴ = cDiag b E s h K W ω := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [cDiag, retainMask]
    split_ifs <;> simp
  · simp [cDiag, hij, Ne.symm hij]

theorem retOut_conj_mul_physF :
    (retOut b E s h K W ω)ᴴ * physF b E s h K W ω = cDiag b E s h K W ω := by
  rw [← cDiag_conjTranspose, ← physF_conj_mul_retOut, conjTranspose_mul,
    conjTranspose_conjTranspose]

theorem retOut_conj_mul_self
    (hS : scatteringMatrix b E W (closeLen s W) ω *
      (scatteringMatrix b E W (closeLen s W) ω)ᴴ = 1) :
    (retOut b E s h K W ω)ᴴ * retOut b E s h K W ω = cDiag b E s h K W ω := by
  rw [retOut, ← farFw_conj_mul_self_sub]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (scatteringMatrix b E W (closeLen s W) ω), hS, Matrix.one_mul,
    farInj_conj_mul_farInj_mul]

theorem dInv_conjTranspose : (dInv b E s K W ω)ᴴ = dInv b E s K W ω := by
  rw [dInv, diagonal_conjTranspose]
  congr 1
  funext k
  simp

theorem sig2_conjTranspose : (sig2 K)ᴴ = sig2 K := by
  rw [sig2, diagonal_conjTranspose]
  congr 1
  funext c
  by_cases hc : c.2 = 0 <;> simp [hc]

theorem retCurrent_conjTranspose : (retCurrent b E s h K W ω)ᴴ = retCurrent b E s h K W ω := by
  simp only [retCurrent, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose,
    dInv_conjTranspose, Matrix.mul_assoc]

/-- `tr J_ret² = 2 Σ_k m_k t_k`. -/
theorem trace_retCurrent_sq
    (hS : scatteringMatrix b E W (closeLen s W) ω *
      (scatteringMatrix b E W (closeLen s W) ω)ᴴ = 1)
    (hlt : ∀ k : Fin K, h ^ 2 < physTseq b E s W ω k.val → physTseq b E s W ω k.val < 1) :
    trace (retCurrent b E s h K W ω * retCurrent b E s h K W ω) =
      ∑ k : Fin K,
        2 * (retainMask K (physTseq b E s W ω) h k * (physTseq b E s W ω k.val : ℂ)) := by
  have hX : physF b E s h K W ω * (physF b E s h K W ω)ᴴ =
      physF b E s h K W ω * (1 : Matrix (Fin K) (Fin K) ℂ) * (physF b E s h K W ω)ᴴ := by
    rw [Matrix.mul_one]
  unfold retCurrent
  rw [hX, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, trace_sub, trace_sub,
    trace_sub, trace_sandwich, trace_sandwich, trace_sandwich, trace_sandwich,
    physF_conj_mul_self, physF_conj_mul_retOut, retOut_conj_mul_physF, retOut_conj_mul_self hS]
  simp only [maskDiag, cDiag, dInv, Matrix.one_mul, Matrix.mul_one, diagonal_mul_diagonal,
    trace_diagonal, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hr : h ^ 2 < physTseq b E s W ω k.val
  · have ht1 := hlt k hr
    have hne : (1 : ℂ) - (physTseq b E s W ω k.val : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.ofReal_ne_zero]; linarith
    simp only [retainMask, hr, ↓reduceIte, one_mul, mul_one]
    push_cast
    field_simp
    ring
  · simp [retainMask, hr]

theorem retCurrent_eq_split
    (hS : scatteringMatrix b E W (closeLen s W) ω *
      (scatteringMatrix b E W (closeLen s W) ω)ᴴ = 1)
    (hcap : ∀ k, K ≤ k → physTseq b E s W ω k ≤ h ^ 2)
    (hlt : ∀ k : Fin K, h ^ 2 < physTseq b E s W ω k.val → physTseq b E s W ω k.val < 1)
    (hh : h ^ 2 < 1) :
    retCurrent b E s h K W ω = (physOutProj b E s W ω - nearPortProj W) -
      farEmbed (omittedProj b E h W (closeLen s W) ω) +
      (farEmbed (closingPairing b E h W (closeLen s W) ω) *
          scatteringMatrix b E W (closeLen s W) ω)ᴴ *
        (farEmbed (closingPairing b E h W (closeLen s W) ω) *
          scatteringMatrix b E W (closeLen s W) ω) := by
  rw [timeS_current_split (K := K) hS hcap hlt hh, retCurrent]; abel

/-- The eigenvalue matrix `Λ = diag(±√t_k)` of an admissible frame. -/
def lamDiag (b E s : ℝ) (K W : ℕ) (ω : GrowthPath W) :
    Matrix (Fin K × Fin 2) (Fin K × Fin 2) ℂ :=
  diagonal fun c => modeEig (physTseq b E s W ω c.1.val) c.2

/-- `Δ = V_sᴴV_s = diag(1_{t_k > h²} √t_k)`. -/
def deltaDiag (b E s h : ℝ) (K W : ℕ) (ω : GrowthPath W) :
    Matrix (Fin K × Fin 2) (Fin K × Fin 2) ℂ :=
  diagonal fun c : Fin K × Fin 2 =>
    if h ^ 2 < physTseq b E s W ω c.1.val then ((Real.sqrt (physTseq b E s W ω c.1.val) : ℝ) : ℂ)
    else 0

/-- **The retained current is the frame current**: `J_ret = V_s 𝖣 V_sᴴ`. -/
theorem retCurrent_eq_frame (Vs : Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (hS : scatteringMatrix b E W (closeLen s W) ω *
      (scatteringMatrix b E W (closeLen s W) ω)ᴴ = 1)
    (hcap : ∀ k, K ≤ k → physTseq b E s W ω k ≤ h ^ 2)
    (hlt : ∀ k : Fin K, h ^ 2 < physTseq b E s W ω k.val → physTseq b E s W ω k.val < 1)
    (hh : h ^ 2 < 1)
    (hG : gramPair (nearPortProj W) Vs =
      curGramOf (initialGram K (Fin 0) (physTseq b E s W ω) h))
    (hE : ∀ x k, ((physOutProj b E s W ω - nearPortProj W) * Vs) x k =
      modeEig (physTseq b E s W ω k.1.val) k.2 * Vs x k) :
    retCurrent b E s h K W ω = Vs * sig2 K * Vsᴴ := by
  have hJV : retCurrent b E s h K W ω * Vs = Vs * lamDiag b E s K W ω := by
    rw [retCurrent_eq_split hS hcap hlt hh, Matrix.add_mul, Matrix.sub_mul,
      omitted_mul_timeSFrame Vs hS hG hE, sub_zero, Matrix.mul_assoc _ _ Vs,
      pairing_mul_timeSFrame Vs hS hG hE, Matrix.mul_zero, add_zero]
    ext x c
    rw [hE x c, lamDiag, mul_diagonal, mul_comm]
  have hVV : Vsᴴ * Vs = deltaDiag b E s h K W ω := by
    have := congrArg Prod.fst hG
    simp only [gramPair, sourceGram] at this
    rw [this, curGram_initialGram_fst _ _ fun k hk => (hlt k hk).le]
    rfl
  have hsum2 : trace (lamDiag b E s K W ω * sig2 K * deltaDiag b E s h K W ω) =
      ∑ k : Fin K,
        2 * (retainMask K (physTseq b E s W ω) h k * (physTseq b E s W ω k.val : ℂ)) := by
    simp only [lamDiag, sig2, deltaDiag, diagonal_mul_diagonal, trace_diagonal,
      Fintype.sum_prod_type, Fin.sum_univ_two]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hr : h ^ 2 < physTseq b E s W ω k.val
    · have h0 : 0 ≤ physTseq b E s W ω k.val := (sq_nonneg h).trans hr.le
      have hsq : ((Real.sqrt (physTseq b E s W ω k.val) : ℝ) : ℂ) *
          ((Real.sqrt (physTseq b E s W ω k.val) : ℝ) : ℂ) = (physTseq b E s W ω k.val : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt h0]
      simp only [modeEig, retainMask, hr, ↓reduceIte, Fin.isValue, one_ne_zero]
      linear_combination 2 * hsq
    · simp [retainMask, hr]
  have hsum3 : trace (sig2 K * deltaDiag b E s h K W ω * sig2 K * deltaDiag b E s h K W ω) =
      ∑ k : Fin K,
        2 * (retainMask K (physTseq b E s W ω) h k * (physTseq b E s W ω k.val : ℂ)) := by
    simp only [sig2, deltaDiag, diagonal_mul_diagonal, trace_diagonal, Fintype.sum_prod_type,
      Fin.sum_univ_two]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hr : h ^ 2 < physTseq b E s W ω k.val
    · have h0 : 0 ≤ physTseq b E s W ω k.val := (sq_nonneg h).trans hr.le
      have hsq : ((Real.sqrt (physTseq b E s W ω k.val) : ℝ) : ℂ) *
          ((Real.sqrt (physTseq b E s W ω k.val) : ℝ) : ℂ) = (physTseq b E s W ω k.val : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt h0]
      simp only [retainMask, hr, ↓reduceIte, Fin.isValue, one_ne_zero]
      linear_combination 2 * hsq
    · simp [retainMask, hr]
  refine eq_frame_of_trace retCurrent_conjTranspose sig2_conjTranspose hJV hVV ?_
  rw [trace_retCurrent_sq hS hlt, hsum2, hsum3]
  ring

end BlockBand.SourceProcess.PhysApprox.B3Cur
