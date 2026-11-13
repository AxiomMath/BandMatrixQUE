module
public import BlockBand.SourceProcess.Stochastic.SourceAlgebra.ProjectionDefect
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Gronwall bound for the projection defect

Quantitative form of the projection-preservation step of the finite Gram law, valid off the
constraint. With `F = P'² - P'`, `τ = Tr P' - Tr P` and the
Frobenius norm, `Φ(V) = ‖F‖² + |τ|²` (`defectLyapunov`). Since `Φ = Re Tr(FᴴF) + conj(τ)τ`
and `F`, `τ` have drift/diffusion `defectDrift`/`defectNoise`, `rankDrift`/`rankNoise`
the product rule gives the Itô drift of `Φ(V_t)`:

  `𝓛Φ = 2 Re Tr(Fᴴ dF) + ∑_a ‖dF_a‖² + 2 Re(conj τ · dτ) + ∑_a |dτ_a|²` (`defectGenerator`).

`defect_generator_le`: for every radius `R` there is `C` with `𝓛Φ(V) ≤ C Φ(V)` whenever
`‖V‖ ≤ R` (Frobenius norm). The constant depends on `R, D₀, Naux, ‖P‖, ‖𝖣‖` and `card ι`
(it is not uniform in the padding dimension). Hypotheses: `0 ≤ D₀`, `IsNearProjection P Naux`,
`𝖣ᴴ = 𝖣`; no constraint on `V`. Proof: the linear representations of `ProjectionDefect` plus
`2 Re⟨F,G⟩ ≤ ‖F‖² + ‖G‖²` and submultiplicativity of the Frobenius norm.
-/

namespace BlockBand.SourceProcess.Stochastic.SourceAlgebra
open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-!
### Frobenius-norm helpers
-/

theorem frob_sq {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [frobenius_norm_def]
  simp_rw [Real.rpow_two]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

theorem frob_single {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (i : m) (j : n) : ‖Matrix.single i j (1 : ℂ)‖ = 1 := by
  have h : ‖Matrix.single i j (1 : ℂ)‖ ^ 2 = 1 := by
    rw [frob_sq]
    simp [single_apply, apply_ite, ite_and, Finset.sum_ite_eq]
  have := norm_nonneg (Matrix.single i j (1 : ℂ))
  nlinarith

theorem frob_entry_le {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) (i : m) (j : n) :
    ‖A i j‖ ≤ ‖A‖ := by
  have h : ‖A i j‖ ^ 2 ≤ ‖A‖ ^ 2 := by
    rw [frob_sq]
    calc ‖A i j‖ ^ 2 ≤ ∑ j', ‖A i j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun j' => ‖A i j'‖ ^ 2) (fun _ _ => by positivity)
            (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', ‖A i' j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun i' => ∑ j', ‖A i' j'‖ ^ 2)
            (fun _ _ => by positivity) (Finset.mem_univ i)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem frob_trace_le {m : Type*} [Fintype m] (A : Matrix m m ℂ) :
    ‖A.trace‖ ≤ Fintype.card m * ‖A‖ := by
  calc ‖A.trace‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : m, ‖A‖ := Finset.sum_le_sum fun i _ => frob_entry_le A i i
    _ = Fintype.card m * ‖A‖ := by simp

theorem frob_mul3_le {k l m n : Type*} [Fintype k] [Fintype l] [Fintype m] [Fintype n] (A : Matrix k l ℂ)
    (B : Matrix l m ℂ) (C : Matrix m n ℂ) : ‖A * B * C‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ :=
  (frobenius_norm_mul _ _).trans
    (mul_le_mul_of_nonneg_right (frobenius_norm_mul _ _) (norm_nonneg _))

theorem frob_mul4_le {k l m n o : Type*} [Fintype k] [Fintype l] [Fintype m] [Fintype n]
    [Fintype o]
    (A : Matrix k l ℂ) (B : Matrix l m ℂ) (C : Matrix m n ℂ) (E : Matrix n o ℂ) :
    ‖A * B * C * E‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ * ‖E‖ :=
  (frobenius_norm_mul _ _).trans (mul_le_mul_of_nonneg_right (frob_mul3_le _ _ _) (norm_nonneg _))

/-- `2 Re(conj z w) ≤ |z|² + |w|²`. -/
theorem two_re_star_mul_le (z w : ℂ) : 2 * (star z * w).re ≤ ‖z‖ ^ 2 + ‖w‖ ^ 2 := by
  have h1 : (star z * w).re ≤ ‖z‖ * ‖w‖ := by
    calc (star z * w).re ≤ ‖star z * w‖ := Complex.re_le_norm _
      _ = ‖z‖ * ‖w‖ := by rw [norm_mul, norm_star]
  nlinarith [sq_nonneg (‖z‖ - ‖w‖)]

/-- `2 Re Tr(FᴴG) ≤ ‖F‖² + ‖G‖²` (Frobenius). -/
theorem two_re_trace_le {m n : Type*} [Fintype m] [Fintype n] (F G : Matrix m n ℂ) :
    2 * (Fᴴ * G).trace.re ≤ ‖F‖ ^ 2 + ‖G‖ ^ 2 := by
  have ht : (Fᴴ * G).trace = ∑ j, ∑ i, star (F i j) * G i j := by
    simp [Matrix.trace, Matrix.mul_apply]
  rw [ht, frob_sq F, frob_sq G, Complex.re_sum, Finset.mul_sum, Finset.sum_comm (f := fun i j =>
    ‖F i j‖ ^ 2), Finset.sum_comm (f := fun i j => ‖G i j‖ ^ 2), ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => two_re_star_mul_le _ _

theorem norm_sourceWeight (D0 : ℝ) (r : Fin 2) : ‖sourceWeight D0 r‖ = Real.sqrt D0 / 2 := by
  rw [sourceWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  split_ifs <;> simp

/-!
### The defect Lyapunov function and its generator
-/

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c]

/-- `Φ(V) = ‖P'² - P'‖² + |Tr P' - Tr P|²` (Frobenius). -/
def defectLyapunov (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (V : Matrix ι c ℂ) : ℝ :=
  ‖projDefect P D V‖ ^ 2 + ‖rankDefect P D V‖ ^ 2

/-- Itô drift of `Φ(V_t)` by the product rule:
`2 Re Tr(Fᴴ dF) + ∑_a ‖dF_a‖² + 2 Re(conj τ dτ) + ∑_a |dτ_a|²`. -/
def defectGenerator (D0 : ℝ) (Naux : ℕ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ)
    (V : Matrix ι c ℂ) : ℝ :=
  2 * ((projDefect P D V)ᴴ * defectDrift D0 Naux P D V).trace.re +
    ∑ a, ‖defectNoise D0 P D a V‖ ^ 2 +
    (2 * (star (rankDefect P D V) * rankDrift D0 Naux P D V).re +
      ∑ a, ‖rankNoise D0 P D a V‖ ^ 2)

/-- The common bound `q = ‖P‖ + R‖𝖣‖R + 1` for `P`, `P'`, `J` and the matrix units. -/
def defectRadius (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (R : ℝ) : ℝ := ‖P‖ + R * ‖D‖ * R + 1

omit [DecidableEq ι] in
theorem current_norm_le {P : Matrix ι ι ℂ} {D : Matrix c c ℂ} {V : Matrix ι c ℂ} {R : ℝ}
    (hV : ‖V‖ ≤ R) : ‖fullCurrent P (gramProjection P V D)‖ ≤ defectRadius P D R := by
  have hR : 0 ≤ R := (norm_nonneg V).trans hV
  rw [fullCurrent_gramProjection, defectRadius]
  calc ‖V * D * Vᴴ‖ ≤ ‖V‖ * ‖D‖ * ‖Vᴴ‖ := frob_mul3_le _ _ _
    _ = ‖V‖ * ‖D‖ * ‖V‖ := by rw [frobenius_norm_conjTranspose]
    _ ≤ R * ‖D‖ * R := by gcongr
    _ ≤ ‖P‖ + R * ‖D‖ * R + 1 := by linarith [norm_nonneg P]

omit [DecidableEq ι] in
theorem gramProjection_norm_le {P : Matrix ι ι ℂ} {D : Matrix c c ℂ} {V : Matrix ι c ℂ} {R : ℝ}
    (hV : ‖V‖ ≤ R) : ‖gramProjection P V D‖ ≤ defectRadius P D R := by
  have hR : 0 ≤ R := (norm_nonneg V).trans hV
  have h := current_norm_le (P := P) (D := D) hV
  rw [fullCurrent_gramProjection] at h
  rw [gramProjection, defectRadius]
  calc ‖P + V * D * Vᴴ‖ ≤ ‖P‖ + ‖V * D * Vᴴ‖ := norm_add_le _ _
    _ ≤ ‖P‖ + R * ‖D‖ * R + 1 := by
      have : ‖V * D * Vᴴ‖ ≤ R * ‖D‖ * R := by
        calc ‖V * D * Vᴴ‖ ≤ ‖V‖ * ‖D‖ * ‖Vᴴ‖ := frob_mul3_le _ _ _
          _ = ‖V‖ * ‖D‖ * ‖V‖ := by rw [frobenius_norm_conjTranspose]
          _ ≤ R * ‖D‖ * R := by gcongr
      linarith

omit [DecidableEq ι] in
theorem one_le_defectRadius (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) {R : ℝ} :
    1 ≤ defectRadius P D R := by
  rw [defectRadius]; nlinarith [norm_nonneg P, norm_nonneg D, mul_self_nonneg R]

/-- Noise bound for `F` (all `V`, `‖V‖ ≤ R`): `‖dF_a‖ ≤ 2√D₀ q³ ‖F‖`. -/
theorem defectNoise_norm_le (D0 : ℝ) {P : Matrix ι ι ℂ} {D : Matrix c c ℂ} (hPH : Pᴴ = P)
    (hPP : P * P = P) (hDH : Dᴴ = D) {V : Matrix ι c ℂ} {R : ℝ} (hV : ‖V‖ ≤ R)
    (a : SourceNoise ι) :
    ‖defectNoise D0 P D a V‖ ≤ 2 * Real.sqrt D0 * defectRadius P D R ^ 3 * ‖projDefect P D V‖ := by
  set q := defectRadius P D R
  have hq0 : 0 ≤ q := le_trans zero_le_one (one_le_defectRadius P D)
  have hq1 : 1 ≤ q := one_le_defectRadius P D
  have hPp := gramProjection_norm_le (P := P) (D := D) hV
  have hJ := current_norm_le (P := P) (D := D) hV
  have hPq : ‖P‖ ≤ q := by
    simp only [q, defectRadius]; nlinarith [norm_nonneg D, mul_self_nonneg R]
  have hE : ‖Matrix.single a.1.2 a.1.1 (1 : ℂ)‖ ≤ q := by rw [frob_single]; exact hq1
  have hE' : ‖Matrix.single a.1.1 a.1.2 (1 : ℂ)‖ ≤ q := by rw [frob_single]; exact hq1
  rw [defectNoise_eq D0 hPH hPP hDH]
  set F := projDefect P D V
  set Pp := gramProjection P V D
  set J := fullCurrent P Pp
  set E := Matrix.single a.1.2 a.1.1 (1 : ℂ)
  set E' := Matrix.single a.1.1 a.1.2 (1 : ℂ)
  calc ‖sourceWeight D0 a.2 • (Pp * E * P * F + F * E * P * J) +
        star (sourceWeight D0 a.2) • (J * P * E' * F + F * P * E' * Pp)‖
      ≤ ‖sourceWeight D0 a.2‖ * (‖Pp * E * P * F‖ + ‖F * E * P * J‖) +
          ‖sourceWeight D0 a.2‖ * (‖J * P * E' * F‖ + ‖F * P * E' * Pp‖) := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, norm_star]
        gcongr <;> exact norm_add_le _ _
    _ ≤ (Real.sqrt D0 / 2) * (q * q * q * ‖F‖ + ‖F‖ * q * q * q) +
          (Real.sqrt D0 / 2) * (q * q * q * ‖F‖ + ‖F‖ * q * q * q) := by
        rw [norm_sourceWeight]
        gcongr
        · exact (frob_mul4_le _ _ _ _).trans (by gcongr)
        · exact (frob_mul4_le _ _ _ _).trans (by gcongr)
        · exact (frob_mul4_le _ _ _ _).trans (by gcongr)
        · exact (frob_mul4_le _ _ _ _).trans (by gcongr)
    _ = 2 * Real.sqrt D0 * q ^ 3 * ‖F‖ := by ring

/-- Noise bound for `τ`: `|dτ_a| ≤ √D₀ (card ι) q² ‖F‖`. -/
theorem rankNoise_norm_le (D0 : ℝ) {P : Matrix ι ι ℂ} {D : Matrix c c ℂ} (hPH : Pᴴ = P)
    (hPP : P * P = P) (hDH : Dᴴ = D) (V : Matrix ι c ℂ) (R : ℝ) (a : SourceNoise ι) :
    ‖rankNoise D0 P D a V‖ ≤
      Real.sqrt D0 * Fintype.card ι * defectRadius P D R ^ 2 * ‖projDefect P D V‖ := by
  set q := defectRadius P D R
  have hq0 : 0 ≤ q := le_trans zero_le_one (one_le_defectRadius P D)
  have hq1 : 1 ≤ q := one_le_defectRadius P D
  have hPq : ‖P‖ ≤ q := by
    simp only [q, defectRadius]; nlinarith [norm_nonneg D, mul_self_nonneg R]
  have hE : ‖Matrix.single a.1.2 a.1.1 (1 : ℂ)‖ ≤ q := by rw [frob_single]; exact hq1
  have hE' : ‖Matrix.single a.1.1 a.1.2 (1 : ℂ)‖ ≤ q := by rw [frob_single]; exact hq1
  rw [rankNoise_eq D0 hPH hPP hDH]
  set F := projDefect P D V
  set E := Matrix.single a.1.2 a.1.1 (1 : ℂ)
  set E' := Matrix.single a.1.1 a.1.2 (1 : ℂ)
  have hPF : ‖P * F‖ ≤ q * ‖F‖ := (frobenius_norm_mul _ _).trans (by gcongr)
  have h1 : ‖E * (P * F)‖ ≤ q * (q * ‖F‖) := (frobenius_norm_mul _ _).trans (by gcongr)
  have h2 : ‖F * P * E'‖ ≤ ‖F‖ * q * q := (frob_mul3_le _ _ _).trans (by gcongr)
  calc ‖sourceWeight D0 a.2 * (E * (P * F)).trace + star (sourceWeight D0 a.2) *
        (F * P * E').trace‖
      ≤ ‖sourceWeight D0 a.2‖ * ‖(E * (P * F)).trace‖ +
          ‖sourceWeight D0 a.2‖ * ‖(F * P * E').trace‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, norm_star]
    _ ≤ (Real.sqrt D0 / 2) * (Fintype.card ι * (q * (q * ‖F‖))) +
          (Real.sqrt D0 / 2) * (Fintype.card ι * (‖F‖ * q * q)) := by
        rw [norm_sourceWeight]
        gcongr
        · exact (frob_trace_le _).trans (by gcongr)
        · exact (frob_trace_le _).trans (by gcongr)
    _ = Real.sqrt D0 * Fintype.card ι * q ^ 2 * ‖F‖ := by ring

omit [DecidableEq ι] in
theorem near_overlap_norm_le {Naux : ℕ} {P : Matrix ι ι ℂ} {D : Matrix c c ℂ}
    {V : Matrix ι c ℂ} {R : ℝ} (hV : ‖V‖ ≤ R) :
    ‖(Naux : ℂ) - (P * gramProjection P V D).trace‖ ≤
      Naux + Fintype.card ι * defectRadius P D R ^ 2 := by
  set q := defectRadius P D R
  have hq0 : 0 ≤ q := le_trans zero_le_one (one_le_defectRadius P D)
  have hPp := gramProjection_norm_le (P := P) (D := D) hV
  have hPq : ‖P‖ ≤ q := by
    simp only [q, defectRadius]; nlinarith [norm_nonneg D, mul_self_nonneg R]
  calc ‖(Naux : ℂ) - (P * gramProjection P V D).trace‖
      ≤ ‖(Naux : ℂ)‖ + ‖(P * gramProjection P V D).trace‖ := norm_sub_le _ _
    _ ≤ Naux + Fintype.card ι * (q * q) := by
        rw [Complex.norm_natCast]
        gcongr
        exact (frob_trace_le _).trans (by gcongr; exact (frobenius_norm_mul _ _).trans (by gcongr))
    _ = Naux + Fintype.card ι * q ^ 2 := by ring

/-- Drift bound for `F`: `‖dF/dt‖ ≤ k (‖F‖ + |τ|)` with an explicit `k`. -/
theorem defectDrift_norm_le {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} (hP : IsNearProjection P Naux) (hDH : Dᴴ = D) {V : Matrix ι c ℂ} {R : ℝ}
    (hV : ‖V‖ ≤ R) :
    ‖defectDrift D0 Naux P D V‖ ≤
      (D0 * Naux / 2 * defectRadius P D R +
          D0 * (Naux + Fintype.card ι * defectRadius P D R ^ 2) * defectRadius P D R +
          D0 / 2 * ((2 * Fintype.card ι + 1) * defectRadius P D R ^ 3)) *
        (‖projDefect P D V‖ + ‖rankDefect P D V‖) := by
  set q := defectRadius P D R
  have hq0 : 0 ≤ q := le_trans zero_le_one (one_le_defectRadius P D)
  have hPp := gramProjection_norm_le (P := P) (D := D) hV
  have hJ := current_norm_le (P := P) (D := D) hV
  have hPq : ‖P‖ ≤ q := by
    simp only [q, defectRadius]; nlinarith [norm_nonneg D, mul_self_nonneg R]
  have hγ := near_overlap_norm_le (Naux := Naux) (P := P) (D := D) hV
  rw [defectDrift_eq hD0 hP hDH]
  set F := projDefect P D V
  set τ := rankDefect P D V
  set Pp := gramProjection P V D
  set J := fullCurrent P Pp
  set z := ‖F‖ + ‖τ‖
  have hFz : ‖F‖ ≤ z := le_add_of_nonneg_right (norm_nonneg _)
  have hτz : ‖τ‖ ≤ z := le_add_of_nonneg_left (norm_nonneg _)
  have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hPF : ‖P * F‖ ≤ q * z := (frobenius_norm_mul _ _).trans (by gcongr)
  have hFP : ‖F * P‖ ≤ z * q := (frobenius_norm_mul _ _).trans (by gcongr)
  have hPpF : ‖Pp * F‖ ≤ q * z := (frobenius_norm_mul _ _).trans (by gcongr)
  have hPP2 : ‖Pp * Pp‖ ≤ q * q := (frobenius_norm_mul _ _).trans (by gcongr)
  have hJPJ : ‖J * P * J‖ ≤ q * q * q := (frob_mul3_le _ _ _).trans (by gcongr)
  have htPF : ‖(P * F).trace‖ ≤ Fintype.card ι * (q * z) := (frob_trace_le _).trans (by gcongr)
  have htF : ‖F.trace + τ‖ ≤ Fintype.card ι * z + z :=
    (norm_add_le _ _).trans (by gcongr; exact (frob_trace_le _).trans (by gcongr))
  have hα : ‖(((-(D0 * Naux / 4)) : ℝ) : ℂ)‖ = D0 * Naux / 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
  have hβ : ‖(((D0 / 2) : ℝ) : ℂ)‖ = D0 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hδ : ‖(D0 : ℂ) * ((Naux : ℂ) - (P * Pp).trace)‖ ≤ D0 * (Naux + Fintype.card ι * q ^ 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hD0]
    gcongr
  calc _ ≤ ‖(((-(D0 * Naux / 4)) : ℝ) : ℂ)‖ * (‖P * F‖ + ‖F * P‖) +
          ‖(D0 : ℂ) * ((Naux : ℂ) - (P * Pp).trace)‖ * ‖Pp * F‖ +
          ‖(((D0 / 2) : ℝ) : ℂ)‖ * (‖(P * F).trace‖ * ‖Pp * Pp‖ + ‖F.trace + τ‖ * ‖J * P * J‖) := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
        · rw [norm_smul]; gcongr; exact norm_add_le _ _
        · rw [norm_smul]
        · rw [norm_smul]; gcongr
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul]
    _ ≤ D0 * Naux / 4 * (q * z + z * q) + D0 * (Naux + Fintype.card ι * q ^ 2) * (q * z) +
          D0 / 2 * (Fintype.card ι * (q * z) * (q * q) + (Fintype.card ι * z + z) * (q * q * q)) := by
        rw [hα, hβ]
        gcongr
    _ = _ := by ring

/-- Drift bound for `τ`. -/
theorem rankDrift_norm_le {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} (hP : IsNearProjection P Naux) (hDH : Dᴴ = D) {V : Matrix ι c ℂ} {R : ℝ}
    (hV : ‖V‖ ≤ R) :
    ‖rankDrift D0 Naux P D V‖ ≤
      D0 / 2 * (Naux + Fintype.card ι * defectRadius P D R ^ 2) * (Fintype.card ι + 1) *
        (‖projDefect P D V‖ + ‖rankDefect P D V‖) := by
  have hγ := near_overlap_norm_le (Naux := Naux) (P := P) (D := D) hV
  rw [rankDrift_eq hD0 hP hDH]
  set F := projDefect P D V
  set τ := rankDefect P D V
  have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have htF : ‖F.trace + τ‖ ≤ Fintype.card ι * (‖F‖ + ‖τ‖) + (‖F‖ + ‖τ‖) :=
    (norm_add_le _ _).trans (add_le_add ((frob_trace_le _).trans (by gcongr; simp))
      (by simp))
  rw [norm_mul, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  calc _ ≤ D0 / 2 * (Naux + Fintype.card ι * defectRadius P D R ^ 2) *
        (Fintype.card ι * (‖F‖ + ‖τ‖) + (‖F‖ + ‖τ‖)) := by gcongr
    _ = _ := by ring

/-- **Gronwall inequality for the projection defect.** For every radius `R` there is a
constant `C` such that `𝓛Φ(V) ≤ C Φ(V)` for every frame with `‖V‖ ≤ R` (Frobenius), where
`Φ = ‖P'² - P'‖² + |Tr P' - Tr P|²` and `𝓛Φ` is its Itô drift under the finite source equation.
No two-projection constraint is assumed. -/
theorem defect_generator_le {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} (hP : IsNearProjection P Naux) (hDH : Dᴴ = D) (R : ℝ) :
    ∃ C : ℝ, ∀ V : Matrix ι c ℂ, ‖V‖ ≤ R →
      defectGenerator D0 Naux P D V ≤ C * defectLyapunov P D V := by
  set q := defectRadius P D R
  set n : ℝ := (Fintype.card ι : ℝ)
  set Na : ℝ := (Fintype.card (SourceNoise ι) : ℝ)
  set k1 := 2 * Real.sqrt D0 * q ^ 3
  set k2 := Real.sqrt D0 * n * q ^ 2
  set k3 := D0 * Naux / 2 * q + D0 * (Naux + n * q ^ 2) * q + D0 / 2 * ((2 * n + 1) * q ^ 3)
  set k4 := D0 / 2 * (Naux + n * q ^ 2) * (n + 1)
  refine ⟨2 + 2 * k3 ^ 2 + 2 * k4 ^ 2 + Na * (k1 ^ 2 + k2 ^ 2), fun V hV => ?_⟩
  set x := ‖projDefect P D V‖
  set y := ‖rankDefect P D V‖
  have hx : 0 ≤ x := norm_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have hΦ : defectLyapunov P D V = x ^ 2 + y ^ 2 := rfl
  have hz : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (x - y)]
  have h1 := two_re_trace_le (projDefect P D V) (defectDrift D0 Naux P D V)
  have h2 : ‖defectDrift D0 Naux P D V‖ ^ 2 ≤ k3 ^ 2 * (x + y) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (defectDrift_norm_le hD0 hP hDH hV) 2
  have h3 : ∑ a, ‖defectNoise D0 P D a V‖ ^ 2 ≤ Na * (k1 ^ 2 * x ^ 2) := by
    calc ∑ a, ‖defectNoise D0 P D a V‖ ^ 2 ≤ ∑ _a : SourceNoise ι, k1 ^ 2 * x ^ 2 := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [← mul_pow]
          exact pow_le_pow_left₀ (norm_nonneg _)
            (defectNoise_norm_le D0 hP.1 hP.2.1 hDH hV a) 2
      _ = Na * (k1 ^ 2 * x ^ 2) := by simp [Na]
  have h4 := two_re_star_mul_le (rankDefect P D V) (rankDrift D0 Naux P D V)
  have h5 : ‖rankDrift D0 Naux P D V‖ ^ 2 ≤ k4 ^ 2 * (x + y) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (rankDrift_norm_le hD0 hP hDH hV) 2
  have h6 : ∑ a, ‖rankNoise D0 P D a V‖ ^ 2 ≤ Na * (k2 ^ 2 * x ^ 2) := by
    calc ∑ a, ‖rankNoise D0 P D a V‖ ^ 2 ≤ ∑ _a : SourceNoise ι, k2 ^ 2 * x ^ 2 := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [← mul_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (rankNoise_norm_le D0 hP.1 hP.2.1 hDH V R a) 2
      _ = Na * (k2 ^ 2 * x ^ 2) := by simp [Na]
  have hNa : 0 ≤ Na := Nat.cast_nonneg _
  have e3 : k3 ^ 2 * (x + y) ^ 2 ≤ k3 ^ 2 * (2 * (x ^ 2 + y ^ 2)) :=
    mul_le_mul_of_nonneg_left hz (sq_nonneg _)
  have e5 : k4 ^ 2 * (x + y) ^ 2 ≤ k4 ^ 2 * (2 * (x ^ 2 + y ^ 2)) :=
    mul_le_mul_of_nonneg_left hz (sq_nonneg _)
  have e1 : Na * (k1 ^ 2 * x ^ 2) ≤ Na * (k1 ^ 2 * (x ^ 2 + y ^ 2)) := by
    gcongr; nlinarith [sq_nonneg y]
  have e2 : Na * (k2 ^ 2 * x ^ 2) ≤ Na * (k2 ^ 2 * (x ^ 2 + y ^ 2)) := by
    gcongr; nlinarith [sq_nonneg y]
  rw [hΦ, defectGenerator]
  linarith [sq_nonneg x, sq_nonneg y]

end BlockBand.SourceProcess.Stochastic.SourceAlgebra
