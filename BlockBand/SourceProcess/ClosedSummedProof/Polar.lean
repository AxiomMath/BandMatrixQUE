module

public import BlockBand.SourceProcess.ContractingWords.AliveLetters
public import BlockBand.SourceProcess.FullSourceStops.CurrentCarrier

/-!
# Polarization of Gram coordinates into rank-one positive letters

Deterministic linear algebra used to read the
Gram coordinates `(VᴴTV)_{ab}` of a frame `V` as traces of Hermitian trace-class letters, so that
the one-layer word estimates `ContractingWords.LayerDrift`/`LayerCov` (stated for Hermitian
letters) apply to them.

* `polVec v w k = v + iᵏw`, `polCoef k = iᵏ/4`, `rk1 u = uu*`;
  **`pol_sum`**: `Σ_k polCoef k • rk1 (polVec v w k) = v w*`.
* `trace_col`: `Tr(v_b v_a* T) = (VᴴTV)_{ab}`; `trace_col_two`:
  `Tr(v_b v_a* X v_d v_c* Y) = (VᴴXV)_{ad}(VᴴYV)_{cb}`.
* `nuclearNorm_rk1`, `nuclearNorm_frameCurrent_le`: `Tr|uu*| = Re Tr uu*`, and
  `Tr|VDVᴴ| ≤ Re Tr VᴴV` for a real diagonal `D` with entries in `[-1,1]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSummedProof

open Matrix Complex
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ComplexOrder

section Pol

variable {ι : Type}

/-- `u_k = v + iᵏ w`. -/
def polVec (v w : ι → ℂ) (k : Fin 4) : ι → ℂ := v + (I ^ (k : ℕ)) • w

/-- `iᵏ/4`. -/
def polCoef (k : Fin 4) : ℂ := I ^ (k : ℕ) / 4

/-- The rank-one positive matrix `uu*`. -/
def rk1 (u : ι → ℂ) : Matrix ι ι ℂ := vecMulVec u (star u)

theorem norm_polCoef (k : Fin 4) : ‖polCoef k‖ = 1 / 4 := by
  simp [polCoef, norm_pow]

/-- **Polarization**: `Σ_k (iᵏ/4) (v + iᵏw)(v + iᵏw)* = v w*`. -/
theorem pol_sum [Fintype ι] (v w : ι → ℂ) : ∑ k, polCoef k • rk1 (polVec v w k) = vecMulVec v (star w) := by
  ext x y
  simp only [Matrix.sum_apply, Matrix.smul_apply, rk1, polVec, polCoef, vecMulVec_apply,
    Fin.sum_univ_four, Pi.add_apply, Pi.smul_apply, Pi.star_apply, star_add, smul_eq_mul,
    star_mul', Complex.star_def, map_pow, Complex.conj_I]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [h3]
  ring_nf
  simp only [I_sq, I_pow_four, Complex.I_pow_three]
  ring_nf
  simp [I_sq]
  ring

theorem posSemidef_rk1 [Fintype ι] (u : ι → ℂ) : (rk1 u).PosSemidef := posSemidef_vecMulVec_self_star u

theorem isHermitian_rk1 [Fintype ι] (u : ι → ℂ) : (rk1 u).IsHermitian := (posSemidef_rk1 u).1

/-- `Tr|uu*| = Re Tr uu* = Σ_x |u_x|²`. -/
theorem nuclearNorm_rk1 [Fintype ι] [DecidableEq ι] (u : ι → ℂ) : nuclearNorm (rk1 u) = ∑ x, ‖u x‖ ^ 2 := by
  rw [ContractingWords.nuclearNorm_of_posSemidef (posSemidef_rk1 u)]
  simp only [rk1, Matrix.trace, diag_apply, vecMulVec_apply, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact_mod_cast rfl

/-- `‖v + iᵏw‖² ≤ 2(‖v‖² + ‖w‖²)` coordinatewise. -/
theorem norm_polVec_sq_le (v w : ι → ℂ) (k : Fin 4) (x : ι) :
    ‖polVec v w k x‖ ^ 2 ≤ 2 * (‖v x‖ ^ 2 + ‖w x‖ ^ 2) := by
  have h : ‖polVec v w k x‖ ≤ ‖v x‖ + ‖w x‖ := by
    simp only [polVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    simp [norm_pow]
  have h0 := norm_nonneg (polVec v w k x)
  nlinarith [norm_nonneg (v x), norm_nonneg (w x), sq_nonneg (‖v x‖ - ‖w x‖)]

end Pol

section Col

variable {ι c : Type*} [Fintype ι] [Fintype c]

omit [Fintype c] in
/-- `Tr(v_b v_a* T) = (VᴴTV)_{ab}`. -/
theorem trace_col (V : Matrix ι c ℂ) (T : Matrix ι ι ℂ) (a b : c) :
    (vecMulVec (fun x => V x b) (star fun x => V x a) * T).trace = (Vᴴ * T * V) a b := by
  simp only [Matrix.trace, diag_apply, mul_apply, vecMulVec_apply, Pi.star_apply,
    conjTranspose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

omit [Fintype c] in
/-- `Tr(v_b v_a* X v_d v_c* Y) = (VᴴXV)_{ad}(VᴴYV)_{cb}`. -/
theorem trace_col_two (V : Matrix ι c ℂ) (X Y : Matrix ι ι ℂ) (a b c' d : c) :
    (vecMulVec (fun x => V x b) (star fun x => V x a) * X *
        (vecMulVec (fun x => V x d) (star fun x => V x c') * Y)).trace =
      (Vᴴ * X * V) a d * (Vᴴ * Y * V) c' b := by
  have e : vecMulVec (fun x => V x b) (star fun x => V x a) * X *
      vecMulVec (fun x => V x d) (star fun x => V x c') =
      ((Vᴴ * X * V) a d) • vecMulVec (fun x => V x b) (star fun x => V x c') := by
    ext x y
    simp only [mul_apply, vecMulVec_apply, Pi.star_apply, Matrix.smul_apply, smul_eq_mul,
      conjTranspose_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun t _ => ?_
    ring
  rw [← Matrix.mul_assoc, e, Matrix.smul_mul, Matrix.trace_smul, trace_col, smul_eq_mul]

end Col

section Current

variable {ι c : Type} [Fintype ι] [DecidableEq ι] [Fintype c] [DecidableEq c]

omit [DecidableEq ι] in
theorem posSemidef_frame_diag (V : Matrix ι c ℂ) (d : c → ℝ) (hd : ∀ x, 0 ≤ d x) :
    (V * diagonal (fun x => (d x : ℂ)) * Vᴴ).PosSemidef := by
  have h : (diagonal (fun x => (d x : ℂ))).PosSemidef :=
    PosSemidef.diagonal (fun x => Complex.zero_le_real.mpr (hd x))
  simpa [Matrix.mul_assoc] using h.mul_mul_conjTranspose_same V

/-- **`Tr|VDVᴴ| ≤ Re Tr VᴴV`** for a real diagonal `D` with entries in `[-1, 1]`. -/
theorem nuclearNorm_frameCurrent_le (V : Matrix ι c ℂ) (d : c → ℝ) (hd : ∀ x, |d x| ≤ 1) :
    nuclearNorm (V * diagonal (fun x => (d x : ℂ)) * Vᴴ) ≤ (Vᴴ * V).trace.re := by
  have hD : (diagonal (fun x => (d x : ℂ))).IsHermitian :=
    isHermitian_diagonal_of_self_adjoint _ (by ext x; simp)
  have hH : (V * diagonal (fun x => (d x : ℂ)) * Vᴴ).IsHermitian :=
    isHermitian_mul_mul_conjTranspose V hD
  have d1 : diagonal (fun x => ((1 - d x : ℝ) : ℂ)) = 1 - diagonal (fun x => (d x : ℂ)) := by
    ext i j; by_cases h : i = j <;> simp [h, one_apply]
  have d2 : diagonal (fun x => ((1 + d x : ℝ) : ℂ)) = 1 + diagonal (fun x => (d x : ℂ)) := by
    ext i j; by_cases h : i = j <;> simp [h, one_apply]
  have e1 : V * Vᴴ - V * diagonal (fun x => (d x : ℂ)) * Vᴴ =
      V * diagonal (fun x => ((1 - d x : ℝ) : ℂ)) * Vᴴ := by
    rw [d1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  have e2 : V * Vᴴ + V * diagonal (fun x => (d x : ℂ)) * Vᴴ =
      V * diagonal (fun x => ((1 + d x : ℝ) : ℂ)) * Vᴴ := by
    rw [d2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
  have h1 : ∀ x, 0 ≤ 1 - d x := fun x => by have := (abs_le.mp (hd x)).2; linarith
  have h2 : ∀ x, 0 ≤ 1 + d x := fun x => by have := (abs_le.mp (hd x)).1; linarith
  have h := FullSourceStops.nuclearNorm_le_of_loewner hH (H := V * Vᴴ)
    (by rw [e1]; exact posSemidef_frame_diag V _ h1) (by rw [e2]; exact posSemidef_frame_diag V _ h2)
  rwa [Matrix.trace_mul_comm] at h

end Current

end BlockBand.SourceProcess.ClosedSummedProof
