module

public import BlockBand.SourceProcess.ClosedSum.SelFrame
public import BlockBand.SourceProcess.ClosedSum.Summed

/-!
# Gram state and eigencolumns of the selected time-`s` frame

For a selection `V` with `IsEigenSel V` and a scattering matrix with `SSᴴ = 1`:
* `farT_eq_of_unitary`: `T_far = S_nfᴴS_nf`;
* **`gramPair_selFrame`** (retained `t_k < 1`): `gramPair P (selFrame) = curGramOf (initialGram …)`;
* **`sub_mul_selFrame`**: `(SᴴPS - P) V_{(k,σ)} = λ_σ(t_k) V_{(k,σ)}`;
* `selT_phys`: at the physical scattering matrix of length `n_s`, `selT = physTseq`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSum

open Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.Closing

variable {W K : ℕ} {V : (Fin W → Fin W → ℂ) → Fin W → Fin (Fintype.card (Fin W)) → ℂ}

/-- With `𝕊ᴴ𝕊 = 1`, `T_far = 1 - S_ffᴴS_ff = S_nfᴴS_nf`. -/
theorem farT_eq_of_unitary {S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hS : Sᴴ * S = 1) :
    farT S = (portBlock S 0 1)ᴴ * portBlock S 0 1 := by
  ext a c
  have h := congrFun (congrFun hS (1, a)) (1, c)
  simp only [mul_apply, conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    one_apply, Prod.mk.injEq, true_and] at h
  simp only [farT, Matrix.sub_apply, mul_apply, conjTranspose_apply, portBlock, of_apply,
    one_apply]
  rw [← h]; ring

theorem outProj_isHermitian (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    (Sᴴ * nearPortProj W * S)ᴴ = Sᴴ * nearPortProj W * S := by
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    nearPortProj_conjTranspose, Matrix.mul_assoc]

theorem outProj_mul_self {S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hS : S * Sᴴ = 1) :
    Sᴴ * nearPortProj W * S * (Sᴴ * nearPortProj W * S) = Sᴴ * nearPortProj W * S := by
  calc Sᴴ * nearPortProj W * S * (Sᴴ * nearPortProj W * S)
      = Sᴴ * nearPortProj W * (S * Sᴴ) * nearPortProj W * S := by simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [hS, Matrix.mul_one, Matrix.mul_assoc _ (nearPortProj W) (nearPortProj W),
          nearPortProj_mul_self]

theorem one_sub_mul_outProj_mul_selF (hV : IsEigenSel V)
    {S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hS : S * Sᴴ = 1) (h : ℝ) :
    (1 - nearPortProj W) * (Sᴴ * nearPortProj W * S) * (farInj W * selFw V S h K) =
      farInj W * selFw V S h K * tDiag K (selT V S) := by
  have e := farInj_conj_outProj_farInj S
  rw [← farT_eq_of_unitary (mul_eq_one_comm.mp hS)] at e
  rw [one_sub_nearPortProj]
  calc farInj W * (farInj W)ᴴ * (Sᴴ * nearPortProj W * S) * (farInj W * selFw V S h K)
      = farInj W * ((farInj W)ᴴ * (Sᴴ * nearPortProj W * S) * farInj W) * selFw V S h K := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [e, Matrix.mul_assoc, farT_mul_selFw hV S h, ← Matrix.mul_assoc]

theorem selF_conj_mul_self (hV : IsEigenSel V) (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (h : ℝ) : (farInj W * selFw V S h K)ᴴ * (farInj W * selFw V S h K) = maskDiag K (selT V S) h := by
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (farInj W)ᴴ, farInj_conj_mul_self,
    Matrix.one_mul, selFw_conj_mul_self hV S h]

/-- **The selected frame has the Gram state of `initialGram`.** -/
theorem gramPair_selFrame (hV : IsEigenSel V) {S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hS : S * Sᴴ = 1) (h : ℝ) (hlt : ∀ k : Fin K, h ^ 2 < selT V S k.val → selT V S k.val < 1) :
    gramPair (nearPortProj W) (selFrame V S h K) =
      curGramOf (initialGram K (Fin 0) (selT V S) h) := by
  rw [selFrame, gramPair_curBlock, gramPair_curFrame (Fin 0) nearPortProj_conjTranspose
    nearPortProj_mul_self (outProj_isHermitian S) (outProj_mul_self hS)
    (by rw [← Matrix.mul_assoc, nearPortProj_mul_farInj, Matrix.zero_mul])
    (selF_conj_mul_self hV S h) (one_sub_mul_outProj_mul_selF hV hS h)
    (fun k hk => ⟨lt_of_le_of_lt (sq_nonneg h) hk, hlt k hk⟩)]

/-- **The selected current columns are `±√t_k` eigenvectors of `P' - P`.** -/
theorem sub_mul_selFrame (hV : IsEigenSel V) {S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hS : S * Sᴴ = 1) (h : ℝ) (hlt : ∀ k : Fin K, h ^ 2 < selT V S k.val → selT V S k.val < 1)
    (x : Fin 2 × Fin W) (k : Fin K × Fin 2) :
    ((Sᴴ * nearPortProj W * S - nearPortProj W) * selFrame V S h K) x k =
      modeEig (selT V S k.1.val) k.2 * selFrame V S h K x k := by
  have := sub_mul_curFrame (Fin 0) nearPortProj_mul_self (outProj_mul_self hS)
    (by rw [← Matrix.mul_assoc, nearPortProj_mul_farInj, Matrix.zero_mul])
    (selF_conj_mul_self hV S h) (one_sub_mul_outProj_mul_selF hV hS h)
    (fun k hk => ⟨lt_of_le_of_lt (sq_nonneg h) hk, hlt k hk⟩) x k.1 k.2
  simpa [selFrame, curBlock, mul_apply] using this

/-- At the physical scattering matrix of length `n_s`, `selT = physTseq`. -/
theorem selT_phys (hV : IsEigenSel V) (b E s : ℝ) (ω : GrowthPath W) :
    selT V (scatteringMatrix b E W (closeLen s W) ω) = physTseq b E s W ω := by
  funext k
  by_cases hk : k < Fintype.card (Fin W)
  · rw [selT_eq hV _ hk]
    simp only [physTseq, hk, ↓reduceDIte]
    rfl
  · rw [selT_ge _ hk]
    simp only [physTseq, hk, ↓reduceDIte]

end BlockBand.SourceProcess.ClosedSum
