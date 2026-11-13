module

public import BlockBand.SourceProcess.Stochastic.FiniteSource
public import Mathlib.Analysis.Matrix.Order

/-!
# The Gram-level characterization of `GramFeasible`

Pure finite-dimensional algebra. Let `𝖣` be Hermitian, `P` an orthogonal projection on a finite
ambient space and `M = VᴴV`, `B = VᴴPV`. Then `P' = P + V𝖣Vᴴ` is Hermitian, and

  `P'P' - P' = PV𝖣Vᴴ + V𝖣VᴴP + V𝖣M𝖣Vᴴ - V𝖣Vᴴ`

vanishes iff its four sandwiches by `V` and `PV` vanish. These sandwiches depend only on `(M, B)`:

* `twoProjection_iff_gram`: `TwoProjection P 𝖣 V` iff `Tr(𝖣M) = 0`,
  `B𝖣M + M𝖣B + M𝖣M𝖣M - M𝖣M = 0`, `B𝖣B + B𝖣M𝖣M = 0` and `B𝖣B + B𝖣M𝖣B = 0`.
* `gramFeasible_of_realization`: a realization on any finite index type gives `GramFeasible`.
* **`gramFeasible_iff`**: `GramFeasible 𝖣 (M, B)` iff `B ⪰ 0`, `M - B ⪰ 0` and the four
  identities above. For `⇐` the realization is `V = [X; Y]`, `P = diag(1, 0)` on `c ⊕ c`, with
  `B = XᴴX` and `M - B = YᴴY`.
* **`isClosed_setOf_gramFeasible`**: the feasible set is closed (entrywise topology).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3Feas

open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open scoped ComplexOrder MatrixOrder

variable {c : Type*} [Fintype c]

/-!
## The idempotence defect and its sandwiches
-/

section Realization

variable {ι : Type*} [Fintype ι] {P : Matrix ι ι ℂ} {D : Matrix c c ℂ}

/-- The defect `P'P' - P'` of `P' = P + V𝖣Vᴴ`. -/
theorem gramProjection_defect (V : Matrix ι c ℂ) (hPP : P * P = P) :
    gramProjection P V D * gramProjection P V D - gramProjection P V D =
      P * V * (D * Vᴴ) + V * (D * Vᴴ * P + D * (Vᴴ * V) * D * Vᴴ - D * Vᴴ) := by
  rw [gramProjection, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hPP]
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_assoc]
  abel

/-- A Hermitian `Z = PVa + Vb` vanishes once its four sandwiches by `V` and `PV` vanish. -/
theorem eq_zero_of_sandwich {Z : Matrix ι ι ℂ} {V : Matrix ι c ℂ} {a b : Matrix c ι ℂ}
    (hPH : Pᴴ = P) (hZH : Zᴴ = Z) (hZ : Z = P * V * a + V * b) (h1 : Vᴴ * Z * V = 0)
    (h2 : Vᴴ * P * Z * V = 0) (h3 : Vᴴ * Z * P * V = 0) (h4 : Vᴴ * P * Z * P * V = 0) :
    Z = 0 := by
  have hU : (Z * V)ᴴ * (Z * V) = 0 := by
    calc (Z * V)ᴴ * (Z * V) = Vᴴ * Z * (Z * V) := by
          rw [conjTranspose_mul, hZH]
      _ = Vᴴ * Z * ((P * V * a + V * b) * V) := by rw [← hZ]
      _ = (Vᴴ * Z * P * V) * (a * V) + (Vᴴ * Z * V) * (b * V) := by
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
      _ = 0 := by rw [h1, h3, Matrix.zero_mul, Matrix.zero_mul, add_zero]
  have hT : (Z * P * V)ᴴ * (Z * P * V) = 0 := by
    calc (Z * P * V)ᴴ * (Z * P * V) = Vᴴ * P * Z * (Z * P * V) := by
          rw [conjTranspose_mul, conjTranspose_mul, hZH, hPH]; simp only [Matrix.mul_assoc]
      _ = Vᴴ * P * Z * ((P * V * a + V * b) * P * V) := by
          rw [← hZ]
      _ = (Vᴴ * P * Z * P * V) * (a * P * V) + (Vᴴ * P * Z * V) * (b * P * V) := by
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
      _ = 0 := by rw [h2, h4, Matrix.zero_mul, Matrix.zero_mul, add_zero]
  have hZV := conjTranspose_mul_self_eq_zero.1 hU
  have hZPV := conjTranspose_mul_self_eq_zero.1 hT
  refine self_mul_conjTranspose_eq_zero.1 ?_
  calc Z * Zᴴ = Z * (P * V * a + V * b) := by rw [hZH, ← hZ]
    _ = (Z * P * V) * a + (Z * V) * b := by
        simp only [Matrix.mul_add, Matrix.mul_assoc]
    _ = 0 := by rw [hZV, hZPV, Matrix.zero_mul, Matrix.zero_mul, add_zero]

/-- **The two-projection constraint in Gram coordinates.** For `𝖣` Hermitian and `P` an
orthogonal projection, `TwoProjection P 𝖣 V` holds iff, with `M = VᴴV` and `B = VᴴPV`,
`Tr(𝖣M) = 0`, `B𝖣M + M𝖣B + M𝖣M𝖣M - M𝖣M = 0`, `B𝖣B + B𝖣M𝖣M = 0` and `B𝖣B + B𝖣M𝖣B = 0`. -/
theorem twoProjection_iff_gram (V : Matrix ι c ℂ) (hPH : Pᴴ = P) (hPP : P * P = P)
    (hDH : Dᴴ = D) :
    TwoProjection P D V ↔
      (D * sourceGram V).trace = 0 ∧
      nearGram P V * D * sourceGram V + sourceGram V * D * nearGram P V +
          sourceGram V * D * sourceGram V * D * sourceGram V -
          sourceGram V * D * sourceGram V = 0 ∧
      nearGram P V * D * nearGram P V +
          nearGram P V * D * sourceGram V * D * sourceGram V = 0 ∧
      nearGram P V * D * nearGram P V +
          nearGram P V * D * sourceGram V * D * nearGram P V = 0 := by
  have hH : (gramProjection P V D)ᴴ = gramProjection P V D := by
    simp only [gramProjection, conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose,
      hPH, hDH, Matrix.mul_assoc]
  have htr : (gramProjection P V D).trace = P.trace ↔ (D * sourceGram V).trace = 0 := by
    have : (V * D * Vᴴ).trace = (D * sourceGram V).trace := by
      rw [trace_mul_comm, sourceGram, ← Matrix.mul_assoc, trace_mul_comm]
    rw [gramProjection, trace_add, this, add_eq_left]
  set Z := gramProjection P V D * gramProjection P V D - gramProjection P V D with hZdef
  have hZ := gramProjection_defect (D := D) V hPP
  rw [← hZdef] at hZ
  have hZH : Zᴴ = Z := by
    rw [hZdef, conjTranspose_sub, conjTranspose_mul, hH]
  have hPP' : ∀ X : Matrix ι c ℂ, P * (P * X) = P * X := fun X => by
    rw [← Matrix.mul_assoc, hPP]
  have e1 : Vᴴ * Z * V = nearGram P V * D * sourceGram V + sourceGram V * D * nearGram P V +
      sourceGram V * D * sourceGram V * D * sourceGram V - sourceGram V * D * sourceGram V := by
    rw [hZ]
    simp only [sourceGram, nearGram, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_assoc]
    abel
  have e2 : Vᴴ * P * Z * V = nearGram P V * D * nearGram P V +
      nearGram P V * D * sourceGram V * D * sourceGram V := by
    rw [hZ]
    simp only [sourceGram, nearGram, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_assoc, hPP']
    abel
  have e4 : Vᴴ * P * Z * P * V = nearGram P V * D * nearGram P V +
      nearGram P V * D * sourceGram V * D * nearGram P V := by
    rw [hZ]
    simp only [sourceGram, nearGram, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_assoc, hPP']
    abel
  have e3 : Vᴴ * Z * P * V = (Vᴴ * P * Z * V)ᴴ := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hZH, hPH, Matrix.mul_assoc]
  have hidem : gramProjection P V D * gramProjection P V D = gramProjection P V D ↔ Z = 0 := by
    rw [hZdef, sub_eq_zero]
  rw [TwoProjection, hidem, htr, ← e1, ← e2, ← e4]
  constructor
  · rintro ⟨-, hZ0, ht⟩
    refine ⟨ht, ?_, ?_, ?_⟩ <;> simp [hZ0]
  · rintro ⟨ht, h1, h2, h4⟩
    refine ⟨hH, eq_zero_of_sandwich hPH hZH hZ h1 h2 ?_ h4, ht⟩
    rw [e3, h2, conjTranspose_zero]

/-- A realization on any finite ambient index type gives a feasible Gram state (reindex the
ambient space by `Fin n`). -/
theorem gramFeasible_of_realization (V : Matrix ι c ℂ) (hPH : Pᴴ = P) (hPP : P * P = P)
    (hT : TwoProjection P D V) : GramFeasible D (gramPair P V) := by
  set e := (Fintype.equivFin ι).symm
  have htr : ∀ X : Matrix ι ι ℂ, (X.submatrix e e).trace = X.trace := fun X => by
    simp only [trace, diag_apply, submatrix_apply]
    exact Equiv.sum_comp e (fun x => X x x)
  set P' := P.submatrix e e
  set V' := V.submatrix e id
  have hVH : V'ᴴ = Vᴴ.submatrix id e := conjTranspose_submatrix _ _ _
  have hproj : gramProjection P' V' D = (gramProjection P V D).submatrix e e := by
    have : V' * D * V'ᴴ = (V * D * Vᴴ).submatrix e e := by
      ext i j
      simp [V', mul_apply]
    rw [gramProjection, gramProjection, this]
    rfl
  have hPP' : P' * P' = (P * P).submatrix e e := submatrix_mul_equiv P P e e e
  obtain ⟨hT1, hT2, hT3⟩ := hT
  refine ⟨Fintype.card ι, P', V', ?_, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [conjTranspose_submatrix, hPH]
  · rw [hPP', hPP]
  · rw [hproj, conjTranspose_submatrix, hT1]
  · rw [hproj, submatrix_mul_equiv, hT2]
  · rw [hproj, htr, htr, hT3]
  · simp only [gramPair, sourceGram, nearGram, Prod.mk.injEq]
    constructor
    · rw [hVH, submatrix_mul_equiv, submatrix_id_id]
    · rw [hVH, submatrix_mul_equiv, submatrix_mul_equiv, submatrix_id_id]

end Realization

/-!
## The Gram-level characterization
-/

/-- **`GramFeasible` in Gram coordinates**. For Hermitian `𝖣`, `(M, B)` is
feasible iff `0 ⪯ B ⪯ M`, `Tr(𝖣M) = 0`, `B𝖣M + M𝖣B + M𝖣M𝖣M - M𝖣M = 0`,
`B𝖣B + B𝖣M𝖣M = 0` and `B𝖣B + B𝖣M𝖣B = 0`. -/
theorem gramFeasible_iff [DecidableEq c] {D : Matrix c c ℂ} (hDH : Dᴴ = D) (G : Matrix c c ℂ × Matrix c c ℂ) :
    GramFeasible D G ↔
      G.2.PosSemidef ∧ (G.1 - G.2).PosSemidef ∧ (D * G.1).trace = 0 ∧
      G.2 * D * G.1 + G.1 * D * G.2 + G.1 * D * G.1 * D * G.1 - G.1 * D * G.1 = 0 ∧
      G.2 * D * G.2 + G.2 * D * G.1 * D * G.1 = 0 ∧
      G.2 * D * G.2 + G.2 * D * G.1 * D * G.2 = 0 := by
  constructor
  · rintro ⟨n, P, V, hPH, hPP, hT, rfl⟩
    have hP : P.PosSemidef := by
      have : P = Pᴴ * P := by rw [hPH, hPP]
      rw [this]; exact posSemidef_conjTranspose_mul_self P
    have h1P : (1 - P).PosSemidef := by
      have : 1 - P = (1 - P)ᴴ * (1 - P) := by
        rw [conjTranspose_sub, conjTranspose_one, hPH, Matrix.sub_mul, Matrix.mul_sub,
          Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hPP, sub_self, sub_zero]
      rw [this]; exact posSemidef_conjTranspose_mul_self _
    exact ⟨nearGram_posSemidef hP V, farGram_posSemidef P V h1P,
      (twoProjection_iff_gram V hPH hPP hDH).1 hT⟩
  · rintro ⟨hB, hMB, ht, h1, h2, h4⟩
    obtain ⟨X, hX⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
    obtain ⟨Y, hY⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hMB.nonneg
    rw [star_eq_conjTranspose] at hX hY
    set V : Matrix (c ⊕ c) c ℂ := fromRows X Y
    set P : Matrix (c ⊕ c) (c ⊕ c) ℂ :=
      diagonal fun i => Sum.elim (fun _ => (1 : ℂ)) (fun _ => 0) i
    have hPH : Pᴴ = P := by
      rw [diagonal_conjTranspose]
      congr 1
      funext i
      rcases i with i | i <;> simp
    have hPP : P * P = P := by
      rw [diagonal_mul_diagonal]
      congr 1
      funext i
      rcases i with i | i <;> simp
    have hPV : P * V = fromRows X 0 := by
      ext i k
      rcases i with i | i <;> simp [P, V, diagonal_mul]
    have hM : sourceGram V = G.1 := by
      rw [sourceGram, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows,
        ← hX, ← hY, add_sub_cancel]
    have hBV : nearGram P V = G.2 := by
      rw [nearGram, Matrix.mul_assoc, hPV, conjTranspose_fromRows_eq_fromCols_conjTranspose,
        fromCols_mul_fromRows, Matrix.mul_zero, add_zero, ← hX]
    have hT : TwoProjection P D V := by
      refine (twoProjection_iff_gram V hPH hPP hDH).2 ?_
      rw [hM, hBV]
      exact ⟨ht, h1, h2, h4⟩
    have hG : gramPair P V = G := by
      rw [gramPair, hM, hBV]
    rw [← hG]
    exact gramFeasible_of_realization V hPH hPP hT

/-- **The feasible set is closed** (entrywise topology on `Matrix c c ℂ × Matrix c c ℂ`). -/
theorem isClosed_setOf_gramFeasible [DecidableEq c] {D : Matrix c c ℂ} (hDH : Dᴴ = D) :
    IsClosed {G : Matrix c c ℂ × Matrix c c ℂ | GramFeasible D G} := by
  have e : {G : Matrix c c ℂ × Matrix c c ℂ | GramFeasible D G} =
      ((Prod.snd ⁻¹' {A | A.PosSemidef}) ∩
        ((fun G : Matrix c c ℂ × Matrix c c ℂ => G.1 - G.2) ⁻¹' {A | A.PosSemidef})) ∩
      ({G | (D * G.1).trace = 0} ∩
        {G | G.2 * D * G.1 + G.1 * D * G.2 + G.1 * D * G.1 * D * G.1 - G.1 * D * G.1 = 0}) ∩
      ({G | G.2 * D * G.2 + G.2 * D * G.1 * D * G.1 = 0} ∩
        {G | G.2 * D * G.2 + G.2 * D * G.1 * D * G.2 = 0}) := by
    ext G
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, gramFeasible_iff hDH G]
    tauto
  rw [e]
  refine ((posSemidef_is_closed.preimage continuous_snd).inter
    (posSemidef_is_closed.preimage (continuous_fst.sub continuous_snd))).inter
    ((isClosed_eq ?_ continuous_const).inter (isClosed_eq ?_ continuous_const)) |>.inter
    ((isClosed_eq ?_ continuous_const).inter (isClosed_eq ?_ continuous_const)) <;> fun_prop

end BlockBand.SourceProcess.PhysApprox.B3Feas
