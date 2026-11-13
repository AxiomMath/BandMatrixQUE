module

public import BlockBand.SourceProcess.ClosedFeas.Base

/-!
# The time-`s` identity `Vs𝖣Vsᴴ = splitCurrent`

`base_split`: at time `s`, a frame with the Gram matrix of `initialGram`, `±√t_k`-eigencolumns of
`𝕊ᴴP𝕊 - P`, `AV = 0` and the whole retained transmission mass carries the retained current
`splitCurrent 𝕊 P A Π`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedFeas

open Matrix BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.ClosedSum
open scoped ComplexOrder

variable {W K : ℕ} {S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {h : ℝ} {t : ℕ → ℝ}

/-- **At time `s` the retained current is carried by the admissible frame** (deterministic).
Hypotheses: unitarity, `h² < 1`, the Gram matrix of `initialGram`, `±√t_k`-eigencolumns of
`𝕊ᴴP𝕊 - P`, `AV = 0`, and equal retained mass `Σ_i φ(t_i) = Σ_{k<K} φ(t_k)` (the cap). -/
theorem base_split (hS : Sᴴ * S = 1) (hS' : S * Sᴴ = 1) (hh : h ^ 2 < 1)
    (ht : ∀ k, 0 ≤ t k ∧ t k ≤ 1) (V : Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (hM : Vᴴ * V = (initialGram K (Fin 0) t h).1.submatrix Sum.inl Sum.inl)
    (hE : ∀ x c, ((Sᴴ * nearPortProj W * S - nearPortProj W) * V) x c =
      modeEig (t c.1.val) c.2 * V x c)
    (hAV : fA h S * V = 0)
    (hsum : ∑ i, retW h (fT_isHermitian (S := S).eigenvalues i) = ∑ k : Fin K, retW h (t k.val)) :
    V * curSig K * Vᴴ = splitCurrent S (nearPortProj W) (fA h S) (fPi h S) := by
  set m : Fin K × Fin 2 → ℂ := fun c => if h ^ 2 < t c.1.val then ((Real.sqrt (t c.1.val) : ℝ) : ℂ)
    else 0 with hm
  have hM' : Vᴴ * V = diagonal m := by
    ext c c'
    rw [hM, submatrix_apply, initialGram_cur _ ht, diagonal_apply]
    by_cases hc : c = c' <;> simp [hc, hm]
  have hcol : ∀ c, ¬ h ^ 2 < t c.1.val → ∀ x, V x c = 0 := by
    intro c hc x
    have h0 : star (fun y => V y c) ⬝ᵥ (fun y => V y c) = 0 := by
      have := congrFun (congrFun hM' c) c
      simp only [mul_apply, conjTranspose_apply, diagonal_apply_eq, hm, hc, ↓reduceIte] at this
      simpa [dotProduct] using this
    exact congrFun (dotProduct_star_self_eq_zero.mp h0) x
  set Λ : Matrix (Fin K × Fin 2) (Fin K × Fin 2) ℂ := diagonal fun c => modeEig (t c.1.val) c.2
  have hJ : (Sᴴ * nearPortProj W * S - nearPortProj W) * V = V * Λ := by
    ext x c; rw [hE, mul_diagonal]; ring
  have hJ' : Sᴴ * nearPortProj W * S * V = nearPortProj W * V + V * Λ := by
    rw [← hJ, Matrix.sub_mul]; abel
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = V * curSig K * Vᴴ := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, X = splitCurrent S (nearPortProj W) (fA h S) (fPi h S) := ⟨_, rfl⟩
  have hsig : curSig K * diagonal m = diagonal fun c => (if c.2 = 0 then 1 else -1) * m c := by
    rw [curSig, diagonal_mul_diagonal]
  have hZV : Z * V = V * Λ := by
    rw [hZ, Matrix.mul_assoc, hM', Matrix.mul_assoc, hsig]
    ext x c
    rw [mul_diagonal, mul_diagonal]
    by_cases hc : h ^ 2 < t c.1.val
    · simp only [hm, hc, ↓reduceIte, modeEig]; split_ifs <;> simp
    · rw [hcol c hc x]; simp
  have hPiSV : fPi h S * (S * V) = 0 := by rw [← Matrix.mul_assoc]; exact pi_mul_eigen hS hAV hJ'
  have hXV : X * V = V * Λ := by
    rw [hX, splitCurrent, Matrix.sub_mul, Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add,
      Matrix.add_mul, hAV, add_zero]
    have h0 : Sᴴ * ((fPi h S)ᴴ * fPi h S) * (S * V) = 0 := by
      simp only [Matrix.mul_assoc, hPiSV, Matrix.mul_zero]
    rw [h0, add_zero, ← Matrix.mul_assoc, hJ']
    abel
  have hsigH : (curSig K)ᴴ = curSig K := by
    rw [curSig, diagonal_conjTranspose]; congr 1; funext c
    simp only [Pi.star_apply]; split_ifs <;> simp
  have hZH : Zᴴ = Z := by
    rw [hZ, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hsigH,
      Matrix.mul_assoc]
  have hXH : Xᴴ = X := by
    rw [hX]
    simp only [splitCurrent, conjTranspose_sub, conjTranspose_add, conjTranspose_mul,
      conjTranspose_conjTranspose, nearPortProj_conjTranspose, fA_conj, Matrix.mul_assoc]
  have hXZ : X * Z = Z * Z := by
    calc X * Z = X * V * curSig K * Vᴴ := by rw [hZ]; simp only [Matrix.mul_assoc]
      _ = Z * V * curSig K * Vᴴ := by rw [hXV, hZV]
      _ = Z * Z := by rw [hZ]; simp only [Matrix.mul_assoc]
  have hsumC : (∑ i, ((retW h (fT_isHermitian (S := S).eigenvalues i) : ℝ) : ℂ)) =
      ∑ k : Fin K, ((retW h (t k.val) : ℝ) : ℂ) := by exact_mod_cast hsum
  have hXsq : (X * X).trace = 2 * ∑ k : Fin K, ((retW h (t k.val) : ℝ) : ℂ) := by
    rw [hX, trace_split_sq hS hS' hh, hsumC]
  have hZsq : (Z * Z).trace = 2 * ∑ k : Fin K, ((retW h (t k.val) : ℝ) : ℂ) := by
    calc (Z * Z).trace = (V * (curSig K * (Vᴴ * V) * curSig K * Vᴴ)).trace := by
          rw [hZ]; simp only [Matrix.mul_assoc]
      _ = (curSig K * (Vᴴ * V) * curSig K * (Vᴴ * V)).trace := by
          rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
      _ = ∑ c : Fin K × Fin 2, ((retW h (t c.1.val) : ℝ) : ℂ) := by
          rw [hM', hsig, curSig, diagonal_mul_diagonal, diagonal_mul_diagonal, trace_diagonal]
          refine Finset.sum_congr rfl fun c _ => ?_
          have h0 := (ht c.1.val).1
          have hs : ((Real.sqrt (t c.1.val) : ℝ) : ℂ) * ((Real.sqrt (t c.1.val) : ℝ) : ℂ) =
              ((t c.1.val : ℝ) : ℂ) := by rw [← Complex.ofReal_mul, Real.mul_self_sqrt h0]
          simp only [hm, retW]
          split_ifs <;> simp [hs]
      _ = _ := by rw [Fintype.sum_prod_type]; simp only [Fin.sum_univ_two]; rw [Finset.mul_sum]
                  exact Finset.sum_congr rfl fun k _ => by ring
  have htr : ((X - Z)ᴴ * (X - Z)).trace = 0 := by
    rw [conjTranspose_sub, hXH, hZH, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, trace_sub,
      trace_sub, trace_sub, Matrix.trace_mul_comm Z X, hXZ, hXsq, hZsq]
    ring
  rw [trace_conjTranspose_mul_self_eq_zero_iff, sub_eq_zero] at htr
  rw [← hZ, ← hX, htr]

end BlockBand.SourceProcess.ClosedFeas
