module

public import BlockBand.Endpoints.Response.NearSchattenFiniteScalar
public import BlockBand.Endpoints.Response.NearSchattenGeneratorMatrix

/-!
# The word generator on clock polynomials is the spectral trace generator

Write `Q = intervalSource`, `P = nearProjection`, `𝕊 = scatteringMatrix`, `J = pathCurrent`
(`= 𝕊*P𝕊 - P`), `A = nearClock = portBlock Q 0 0`, `Σ' = nsgProjBlock 𝕊 = portBlock(𝕊*P𝕊) 0 0`,
`T(m) = Tr A^m`, `U(m) = Tr(A^m Σ')`, `D = transportD0`.

* `nsfClockPoly a N = Σ_{r<N} a_r Tr (QP)^{r+1}`, the clock polynomial of
  `π(x) = Σ_r a_r x^{r+1}`; `nsf_isOrdinaryPoly_clockPoly`.
* `nsf_polyValue_wordDrift_clockWord` (the `wordDrift` identity):
  `wordDrift((QP)^{r+1}) ↦ -(D/2) g (r+1) T(r+1) + (D/2)(r+1) Σ_{l<r} T(l+1) U(r-l)`
  (`g = ½ Tr J²`).
* `nsf_polyValue_wordGenerator_clockPoly`: `𝒜_t Φ_π ↦ Σ_r a_r wordDrift((QP)^{r+1})` when
  `q(t) = 0` (injection off; the `wordCov` part vanishes since `Φ_π` is linear).
* `nsf_polyValue_wordGenerator_frame`: in any unitary eigenframe `(V, λ)` of `A`,
  `𝒜_t Φ_π ↦ nsfSpecGen D g π' π'' λ S^V` with `S^V_jj = Re (V*Σ'V)_jj` and
  `g = nsgConductance 𝕊`. In particular the spectral value at a polynomial does not depend on the
  frame (`nsf_specGen_poly_frame_indep`).
* `nsfGenExpr d₁ d₂`: the path expression of `nsgGenExpr` for a general `C²` function
  (`nsf_nsgGenExpr_eq`: `nsgGenExpr = nsfGenExpr f_ε' f_ε''`), and
  `nsf_polyValue_wordGenerator_path`: `polyValue(𝒜_t Φ_π) = nsfGenExpr π' π''` at the path.
* `nsf_polyValue_clockPoly`: `Φ_π ↦ Σ_i π(λ_i)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Matrix Finset
open scoped ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

/-!
## The clock polynomial
-/

/-- `Φ_π = Σ_{r<N} a_r Tr (QP)^{r+1}` for `π(x) = Σ_r a_r x^{r+1}`. -/
def nsfClockPoly (a : ℕ → ℝ) (N : ℕ) : TracePoly 0 1 :=
  ∑ r ∈ range N, MvPolynomial.C ((a r : ℝ) : ℂ) * MvPolynomial.X (clockWord (r + 1))

theorem nsf_vars_clockPoly (a : ℕ → ℝ) (N : ℕ) :
    ∀ w ∈ (nsfClockPoly a N).vars, ∃ r ∈ range N, w = clockWord (r + 1) := by
  intro w hw
  unfold nsfClockPoly at hw
  obtain ⟨r, hr, hw'⟩ := Finset.mem_biUnion.1 (MvPolynomial.vars_sum_subset _ _ hw)
  rcases Finset.mem_union.1 (MvPolynomial.vars_mul _ _ hw') with h | h
  · rw [MvPolynomial.vars_C] at h; simp at h
  · rw [MvPolynomial.vars_X, Finset.mem_singleton] at h
    exact ⟨r, hr, h⟩

theorem nsf_isOrdinaryPoly_clockPoly (a : ℕ → ℝ) (N : ℕ) :
    IsOrdinaryPoly (nsfClockPoly a N) := by
  intro w hw
  obtain ⟨r, -, rfl⟩ := nsf_vars_clockPoly a N w hw
  exact ns_isOrdinaryWord_clockWord (by omega)

theorem nsf_pderiv_clockPoly (a : ℕ → ℝ) (N : ℕ) (w : ClockWord) :
    MvPolynomial.pderiv w (nsfClockPoly a N) =
      ∑ r ∈ range N, MvPolynomial.C ((a r : ℝ) : ℂ) *
        (if clockWord (r + 1) = w then 1 else 0) := by
  unfold nsfClockPoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X, Pi.single_apply]

theorem nsf_pderiv_pderiv_clockPoly (a : ℕ → ℝ) (N : ℕ) (w v : ClockWord) :
    MvPolynomial.pderiv v (MvPolynomial.pderiv w (nsfClockPoly a N)) = 0 := by
  rw [nsf_pderiv_clockPoly, map_sum]
  refine Finset.sum_eq_zero fun r _ => ?_
  split_ifs
  · rw [mul_one, MvPolynomial.pderiv_C]
  · rw [mul_zero, map_zero]

/-- First-order part of `wordGenerator` at a linear clock polynomial. -/
theorem nsf_sum_vars_pderiv_mul (a : ℕ → ℝ) (N : ℕ) (G : ClockWord → TracePoly 0 1) :
    ∑ w ∈ (nsfClockPoly a N).vars, MvPolynomial.pderiv w (nsfClockPoly a N) * G w =
      ∑ r ∈ range N, MvPolynomial.C ((a r : ℝ) : ℂ) * G (clockWord (r + 1)) := by
  classical
  set S := (nsfClockPoly a N).vars ∪ (range N).image fun r => clockWord (r + 1)
  rw [Finset.sum_subset (Finset.subset_union_left (s₂ := (range N).image fun r => clockWord (r + 1)))
    fun w _ hw => by rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars hw, zero_mul]]
  simp only [nsf_pderiv_clockPoly, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r hr => ?_
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq, ite_eq_left_iff.2 fun h =>
    absurd (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hr)) h]

/-!
## Values of clock words
-/

section Path

variable (b E : ℝ) (q : ℝ → ℝ) (W j : ℕ) (ω : GrowthPath W) (κ : Fin 0 → ℕ)

/-- The letter `(Q, P)` of clock words. -/
abbrev nsf_x1 : TraceLetter 0 1 × Separator := (TraceLetter.interval 0, Separator.proj)

theorem nsf_clockWord_eq (k : ℕ) : clockWord k = List.replicate k nsf_x1 := rfl

/-- The matrix `A_i B_i` of a letter of the one-source family. -/
abbrev nsf_lm (x : TraceLetter 0 1 × Separator) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  letterMatrix b E κ (fun _ => q) W j ω x.1 * separatorMatrix b E W j ω x.2

theorem nsf_wordValue_eq (L : TraceWord 0 1) :
    wordValue b E κ (fun _ => q) W j ω L = ((L.map (nsf_lm b E q W j ω κ)).prod).trace := rfl

theorem nsf_prod_replicate (m : ℕ) :
    ((List.replicate m nsf_x1).map (nsf_lm b E q W j ω κ)).prod =
      (intervalSource b E W j q ω * nearProjection W) ^ m := by
  rw [List.map_replicate, List.prod_replicate]
  rfl

theorem nsf_setLastSep_replicate (m : ℕ) :
    setLastSep (List.replicate m nsf_x1) .proj = List.replicate m nsf_x1 := by
  cases m with
  | zero => rfl
  | succ c =>
    unfold setLastSep
    rw [List.dropLast_replicate, List.getLast?_replicate]
    simp [List.replicate_succ']

theorem nsf_sepAt_replicate {m i : ℕ} (h : i < m) :
    sepAt (List.replicate m nsf_x1) i = Separator.proj := by
  unfold sepAt
  rw [List.getD_replicate _ h]

theorem nsf_prod_replicate_current (m : ℕ) :
    ((List.replicate m nsf_x1 ++ [(TraceLetter.current, Separator.proj)]).map
        (nsf_lm b E q W j ω κ)).prod =
      (intervalSource b E W j q ω * nearProjection W) ^ m *
        (pathCurrent b E W j ω * nearProjection W) := by
  rw [List.map_append, List.prod_append, nsf_prod_replicate]
  simp [nsf_lm, letterMatrix, separatorMatrix]

/-- `T(m) = Tr A^m`. -/
def nsfT (m : ℕ) : ℂ := ((nearClock b E W j q ω) ^ m).trace

/-- `U(m) = Tr(A^m Σ')`, `Σ' = portBlock(𝕊*P𝕊) 0 0`. -/
def nsfU (m : ℕ) : ℂ :=
  ((nearClock b E W j q ω) ^ m * nsgProjBlock (scatteringMatrix b E W j ω)).trace

theorem nsf_trace_QP_pow {m : ℕ} (hm : 1 ≤ m) :
    ((intervalSource b E W j q ω * nearProjection W) ^ m).trace = nsfT b E q W j ω m :=
  ns_trace_QP_pow W _ hm

/-- `Tr (QP)^m + Tr((QP)^m J P) = Tr(A^m Σ')` for `m ≥ 1`. -/
theorem nsf_trace_QP_pow_add_current {m : ℕ} (hm : 1 ≤ m) :
    ((intervalSource b E W j q ω * nearProjection W) ^ m).trace +
        ((intervalSource b E W j q ω * nearProjection W) ^ m *
          (pathCurrent b E W j ω * nearProjection W)).trace = nsfU b E q W j ω m := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' hm
  set Q := intervalSource b E W j q ω
  set S := scatteringMatrix b E W j ω
  set V := nsNearIncl W
  have hP : nearProjection W = V * Vᴴ := ns_nearProjection_eq W
  have hX : (Q * nearProjection W) ^ (c + 1) * nearProjection W =
      (Q * nearProjection W) ^ (c + 1) := by
    rw [pow_succ, Matrix.mul_assoc, Matrix.mul_assoc, tcs_nearProjection_idem]
  have hm : (Q * nearProjection W) ^ (c + 1) +
      (Q * nearProjection W) ^ (c + 1) * (pathCurrent b E W j ω * nearProjection W) =
      (Q * nearProjection W) ^ (c + 1) * (Sᴴ * nearProjection W * S) * nearProjection W := by
    calc (Q * nearProjection W) ^ (c + 1) +
          (Q * nearProjection W) ^ (c + 1) * (pathCurrent b E W j ω * nearProjection W) =
        (Q * nearProjection W) ^ (c + 1) * nearProjection W +
          (Q * nearProjection W) ^ (c + 1) * (pathCurrent b E W j ω * nearProjection W) := by
          rw [hX]
      _ = (Q * nearProjection W) ^ (c + 1) *
          ((nearProjection W + pathCurrent b E W j ω) * nearProjection W) := by
          rw [Matrix.add_mul, tcs_nearProjection_idem, Matrix.mul_add]
      _ = _ := by
          unfold pathCurrent
          rw [add_sub_cancel]
          simp only [Matrix.mul_assoc, S]
  rw [← Matrix.trace_add, hm, ns_QP_pow_succ]
  set A := Vᴴ * Q * V with hA
  set P' := Sᴴ * nearProjection W * S with hP'
  have e : Q * V * A ^ c * Vᴴ * P' * nearProjection W = (Q * V * A ^ c * Vᴴ * P' * V) * Vᴴ := by
    rw [hP]; simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm]
  unfold nsfU nsgProjBlock nearClock
  rw [ns_portBlock_eq, ns_portBlock_eq, pow_succ', hA, hP']
  simp only [Matrix.mul_assoc, Q, S, V]

/-- `g`-word: `polyValue gPoly = ½ Tr J²`. -/
theorem nsf_polyValue_gPoly :
    polyValue b E κ (fun _ => q) W j ω (gPoly : TracePoly 0 1) =
      (1 / 2 : ℂ) * ((pathCurrent b E W j ω) ^ 2).trace := by
  unfold gPoly polyValue
  simp only [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [nsf_wordValue_eq]
  simp [nsf_lm, letterMatrix, separatorMatrix, sq]

/-- `pairTerm` on `(QP)^{r+1}` for `i < j' < r+1`. -/
theorem nsf_polyValue_pairTerm (D0 : ℝ) (r i j' : ℕ) (hij : i < j') (hj : j' < r + 1) :
    polyValue b E κ (fun _ => q) W j ω (pairTerm D0 (clockWord (r + 1)) i j') =
      ((D0 / 2 : ℝ) : ℂ) * (nsfT b E q W j ω (r + 1 - (j' - i)) * nsfU b E q W j ω (j' - i) +
        nsfU b E q W j ω (r + 1 - (j' - i)) * nsfT b E q W j ω (j' - i)) := by
  unfold pairTerm polyValue
  dsimp only
  rw [nsf_clockWord_eq, List.rotate_replicate, List.rotate_replicate, List.take_replicate,
    List.take_replicate, List.length_replicate, nsf_sepAt_replicate (by omega),
    nsf_sepAt_replicate (by omega),
    show min (r + 1 - (j' - i)) (r + 1) = r + 1 - (j' - i) by omega,
    show min (j' - i) (r + 1) = j' - i by omega, nsf_setLastSep_replicate,
    nsf_setLastSep_replicate]
  simp only [map_mul, map_add, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [nsf_wordValue_eq, nsf_wordValue_eq, nsf_wordValue_eq, nsf_wordValue_eq,
    nsf_prod_replicate, nsf_prod_replicate, nsf_prod_replicate_current,
    nsf_prod_replicate_current, nsf_trace_QP_pow_add_current _ _ _ _ _ _ (by omega),
    nsf_trace_QP_pow_add_current _ _ _ _ _ _ (by omega), nsf_trace_QP_pow _ _ _ _ _ _ (by omega),
    nsf_trace_QP_pow _ _ _ _ _ _ (by omega)]

/-- **The wordDrift identity**:
`wordDrift((QP)^{r+1}) ↦ -(D/2) g (r+1) T(r+1) + (D/2)(r+1) Σ_{l<r} T(l+1) U(r-l)`,
`g = ½ Tr J²`.
-/
theorem nsf_polyValue_wordDrift_clockWord (D0 : ℝ) (r : ℕ) :
    polyValue b E κ (fun _ => q) W j ω (wordDrift D0 (clockWord (r + 1))) =
      -(((D0 / 2 : ℝ) : ℂ) * ((1 / 2 : ℂ) * ((pathCurrent b E W j ω) ^ 2).trace) *
          ((r : ℂ) + 1) * nsfT b E q W j ω (r + 1)) +
        ((D0 / 2 : ℝ) : ℂ) * (((r : ℂ) + 1) *
          ∑ l ∈ range r, nsfT b E q W j ω (l + 1) * nsfU b E q W j ω (r - l)) := by
  unfold wordDrift
  have hc : (clockWord (r + 1)).countP (fun x => decide (x.2 = Separator.proj)) = r + 1 := by
    rw [nsf_clockWord_eq, List.countP_replicate]
    simp
  have hlen : (clockWord (r + 1)).length = r + 1 := by
    rw [nsf_clockWord_eq, List.length_replicate]
  rw [hc, hlen]
  have hT : polyValue b E κ (fun _ => q) W j ω (wv (clockWord (r + 1))) =
      nsfT b E q W j ω (r + 1) := by
    unfold polyValue wv
    rw [MvPolynomial.eval_X, ns_wordValue_clockWord_eq b E q W j ω κ (by omega)]
    rfl
  have hpairs : polyValue b E κ (fun _ => q) W j ω
      (∑ i ∈ range (r + 1), ∑ j' ∈ Ioo i (r + 1), pairTerm D0 (clockWord (r + 1)) i j') =
      ((D0 / 2 : ℝ) : ℂ) * (((r : ℂ) + 1) *
        ∑ l ∈ range r, nsfT b E q W j ω (l + 1) * nsfU b E q W j ω (r - l)) := by
    unfold polyValue
    rw [map_sum]
    simp only [map_sum]
    rw [← nsf_sum_pairs_sym, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j' hj' => ?_
    have := Finset.mem_Ioo.1 hj'
    exact nsf_polyValue_pairTerm b E q W j ω κ D0 r i j' this.1 this.2
  have hg := nsf_polyValue_gPoly b E q W j ω κ
  unfold polyValue at hT hpairs hg ⊢
  rw [map_add, map_neg, hpairs]
  simp only [map_mul, MvPolynomial.eval_C, hg, hT]
  push_cast
  ring

/-- The injection vanishes on clock words when `q(t) = 0`. -/
theorem nsf_wordInjection_clockWord (t : ℝ) (hq : q t = 0) (r : ℕ) :
    wordInjection b (fun _ : Fin 1 => q) t (clockWord (r + 1)) = 0 := by
  rcases r with _ | r
  · show (if Separator.proj = .id ∨ Separator.proj = .proj then
      ((dStar b * q t : ℝ) : ℂ) else 0) = 0
    rw [hq, mul_zero, Complex.ofReal_zero, ite_self]
  · rw [nsf_clockWord_eq, List.replicate_succ, List.replicate_succ]
    rfl

/-- The word generator of a clock polynomial after the injection (`q(t) = 0`):
`𝒜_t Φ_π ↦ Σ_r a_r wordDrift((QP)^{r+1})`. -/
theorem nsf_polyValue_wordGenerator_clockPoly (a : ℕ → ℝ) (N : ℕ) (t : ℝ) (hq : q t = 0) :
    polyValue b E κ (fun _ => q) W j ω (wordGenerator b E (fun _ => q) t (nsfClockPoly a N)) =
      ∑ r ∈ range N, ((a r : ℝ) : ℂ) *
        polyValue b E κ (fun _ => q) W j ω (wordDrift (transportD0 b E) (clockWord (r + 1))) := by
  unfold wordGenerator
  rw [nsf_sum_vars_pderiv_mul]
  simp only [nsf_pderiv_pderiv_clockPoly, zero_mul, Finset.sum_const_zero, mul_zero, add_zero,
    nsf_wordInjection_clockWord b q t hq, map_zero]
  unfold polyValue
  rw [map_sum]
  simp only [map_mul, MvPolynomial.eval_C]

end Path

/-!
## Spectral form in a unitary eigenframe
-/

theorem nsf_nearProjection_isHermitian (W : ℕ) : (nearProjection W).IsHermitian :=
  tcs_nearProjection_hermitian W

theorem nsf_projBlock_isHermitian {W : ℕ} (U : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    (nsgProjBlock U).IsHermitian := by
  unfold nsgProjBlock
  rw [ns_portBlock_eq]
  exact isHermitian_conjTranspose_mul_mul _
    (isHermitian_conjTranspose_mul_mul _ (nsf_nearProjection_isHermitian W))

theorem nsf_frameDiag_coe {W : ℕ} (U : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (V : Matrix (Fin W) (Fin W) ℂ) (i : Fin W) :
    ((nsgFrameDiag U V i : ℝ) : ℂ) = (Vᴴ * nsgProjBlock U * V) i i := by
  have h := (isHermitian_conjTranspose_mul_mul V (nsf_projBlock_isHermitian U)).coe_re_apply_self i
  unfold nsgFrameDiag
  simpa using h

/-- `½ Tr J² = g` (as complex numbers; `J` is Hermitian). -/
theorem nsf_half_trace_current_sq (b E : ℝ) (W j : ℕ) (ω : GrowthPath W) :
    (1 / 2 : ℂ) * ((pathCurrent b E W j ω) ^ 2).trace =
      ((nsgConductance (scatteringMatrix b E W j ω) : ℝ) : ℂ) := by
  have hJ : (pathCurrent b E W j ω).IsHermitian := by
    unfold pathCurrent
    exact (isHermitian_conjTranspose_mul_mul _ (nsf_nearProjection_isHermitian W)).sub
      (nsf_nearProjection_isHermitian W)
  have h2 := hJ.pow 2
  have hre : (((pathCurrent b E W j ω ^ 2).trace).re : ℂ) = (pathCurrent b E W j ω ^ 2).trace := by
    unfold Matrix.trace
    rw [Complex.re_sum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simpa using h2.coe_re_apply_self i
  rw [nsg_pathCurrent_eq, ← hre]
  push_cast
  simp only [Complex.ofReal_re]
  ring

/-- Powers in a unitary frame: `A = V diag(λ) V*` gives `A^m = V diag(λ^m) V*`. -/
theorem nsf_pow_frame {W : ℕ} {A V : Matrix (Fin W) (Fin W) ℂ} (hV : Vᴴ * V = 1) {lam : Fin W → ℝ}
    (hA : A = V * diagonal (fun i => (lam i : ℂ)) * Vᴴ) (m : ℕ) :
    A ^ m = V * diagonal (fun i => ((lam i ^ m : ℝ) : ℂ)) * Vᴴ := by
  have hV' : V * Vᴴ = 1 := mul_eq_one_comm.mp hV
  induction m with
  | zero => simp [hV']
  | succ m ih =>
    rw [pow_succ, ih, hA]
    calc V * diagonal (fun i => ((lam i ^ m : ℝ) : ℂ)) * Vᴴ *
          (V * diagonal (fun i => (lam i : ℂ)) * Vᴴ) =
        V * (diagonal (fun i => ((lam i ^ m : ℝ) : ℂ)) * (Vᴴ * V) *
          diagonal (fun i => (lam i : ℂ))) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hV, Matrix.mul_one, diagonal_mul_diagonal]
        congr 3
        ext i
        push_cast
        ring

section Frame

variable (b E : ℝ) (q : ℝ → ℝ) (W j : ℕ) (ω : GrowthPath W) (κ : Fin 0 → ℕ)

theorem nsf_T_frame {V : Matrix (Fin W) (Fin W) ℂ} (hV : Vᴴ * V = 1) {lam : Fin W → ℝ}
    (hA : nearClock b E W j q ω = V * diagonal (fun i => (lam i : ℂ)) * Vᴴ) (m : ℕ) :
    nsfT b E q W j ω m = ((∑ i, lam i ^ m : ℝ) : ℂ) := by
  unfold nsfT
  rw [nsf_pow_frame hV hA, Matrix.trace_mul_cycle, hV, Matrix.one_mul, trace_diagonal]
  push_cast
  rfl

theorem nsf_U_frame {V : Matrix (Fin W) (Fin W) ℂ} (hV : Vᴴ * V = 1) {lam : Fin W → ℝ}
    (hA : nearClock b E W j q ω = V * diagonal (fun i => (lam i : ℂ)) * Vᴴ) (m : ℕ) :
    nsfU b E q W j ω m =
      ((∑ i, lam i ^ m * nsgFrameDiag (scatteringMatrix b E W j ω) V i : ℝ) : ℂ) := by
  unfold nsfU
  rw [nsf_pow_frame hV hA]
  have e : V * diagonal (fun i => ((lam i ^ m : ℝ) : ℂ)) * Vᴴ *
      nsgProjBlock (scatteringMatrix b E W j ω) =
      V * (diagonal (fun i => ((lam i ^ m : ℝ) : ℂ)) *
        (Vᴴ * nsgProjBlock (scatteringMatrix b E W j ω) * V)) * Vᴴ := by
    have hV' : V * Vᴴ = 1 := mul_eq_one_comm.mp hV
    calc _ = V * diagonal (fun i => ((lam i ^ m : ℝ) : ℂ)) * Vᴴ *
          nsgProjBlock (scatteringMatrix b E W j ω) * (V * Vᴴ) := by rw [hV', Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_cycle, hV, Matrix.one_mul]
  unfold Matrix.trace
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [diag_apply, diagonal_mul, nsf_frameDiag_coe]

/-- The word generator of a clock polynomial in a unitary eigenframe: after the injection
(`q(t) = 0`), for any unitary `V` and real `λ` with `A = V diag(λ) V*`,
`polyValue(𝒜_t Φ_π) = nsfSpecGen D g π' π'' λ S^V`. -/
theorem nsf_polyValue_wordGenerator_frame (a : ℕ → ℝ) (N : ℕ) (t : ℝ) (hq : q t = 0)
    {V : Matrix (Fin W) (Fin W) ℂ} (hV : Vᴴ * V = 1) {lam : Fin W → ℝ}
    (hA : nearClock b E W j q ω = V * diagonal (fun i => (lam i : ℂ)) * Vᴴ) :
    polyValue b E κ (fun _ => q) W j ω (wordGenerator b E (fun _ => q) t (nsfClockPoly a N)) =
      ((nsfSpecGen (transportD0 b E) (nsgConductance (scatteringMatrix b E W j ω))
        (nsfPolyD1 a N) (nsfPolyD2 a N) lam (nsgFrameDiag (scatteringMatrix b E W j ω) V) :
          ℝ) : ℂ) := by
  rw [nsf_polyValue_wordGenerator_clockPoly b E q W j ω κ a N t hq, nsf_specGen_poly]
  simp only [nsf_polyValue_wordDrift_clockWord, nsf_half_trace_current_sq,
    nsf_T_frame b E q W j ω hV hA, nsf_U_frame b E q W j ω hV hA]
  push_cast
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

/-- Frame independence of the spectral form at a polynomial: two unitary eigenframes of the clock
give the same value (both equal the frame-free moment form of `nsf_specGen_poly`). -/
theorem nsf_specGen_poly_frame_indep (a : ℕ → ℝ) (N : ℕ)
    {V V' : Matrix (Fin W) (Fin W) ℂ} (hV : Vᴴ * V = 1) (hV' : V'ᴴ * V' = 1)
    {lam lam' : Fin W → ℝ}
    (hA : nearClock b E W j q ω = V * diagonal (fun i => (lam i : ℂ)) * Vᴴ)
    (hA' : nearClock b E W j q ω = V' * diagonal (fun i => (lam' i : ℂ)) * V'ᴴ) :
    nsfSpecGen (transportD0 b E) (nsgConductance (scatteringMatrix b E W j ω))
        (nsfPolyD1 a N) (nsfPolyD2 a N) lam (nsgFrameDiag (scatteringMatrix b E W j ω) V) =
      nsfSpecGen (transportD0 b E) (nsgConductance (scatteringMatrix b E W j ω))
        (nsfPolyD1 a N) (nsfPolyD2 a N) lam' (nsgFrameDiag (scatteringMatrix b E W j ω) V') := by
  have hT : ∀ m, ∑ i, lam i ^ m = ∑ i, lam' i ^ m := fun m => Complex.ofReal_injective
    ((nsf_T_frame b E q W j ω hV hA m).symm.trans (nsf_T_frame b E q W j ω hV' hA' m))
  have hU : ∀ m, ∑ i, lam i ^ m * nsgFrameDiag (scatteringMatrix b E W j ω) V i =
      ∑ i, lam' i ^ m * nsgFrameDiag (scatteringMatrix b E W j ω) V' i :=
    fun m => Complex.ofReal_injective
      ((nsf_U_frame b E q W j ω hV hA m).symm.trans (nsf_U_frame b E q W j ω hV' hA' m))
  rw [nsf_specGen_poly, nsf_specGen_poly]
  simp only [hT, hU]

/-- The polynomial trace `Tr π(A) = Σ_i π(λ_i)` as the value of the clock polynomial. -/
theorem nsf_polyValue_clockPoly (a : ℕ → ℝ) (N : ℕ) {V : Matrix (Fin W) (Fin W) ℂ}
    (hV : Vᴴ * V = 1) {lam : Fin W → ℝ}
    (hA : nearClock b E W j q ω = V * diagonal (fun i => (lam i : ℂ)) * Vᴴ) :
    polyValue b E κ (fun _ => q) W j ω (nsfClockPoly a N) =
      ((∑ i, nsfPolyFun a N (lam i) : ℝ) : ℂ) := by
  unfold nsfClockPoly polyValue nsfPolyFun
  rw [map_sum]
  simp only [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  simp only [ns_wordValue_clockWord_eq b E q W j ω κ (Nat.le_add_left 1 _)]
  simp only [show ∀ r, ((nearClock b E W j q ω) ^ (r + 1)).trace = nsfT b E q W j ω (r + 1)
    from fun r => rfl, nsf_T_frame b E q W j ω hV hA]
  push_cast
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

end Frame

/-!
## At the path, in the eigenframe of `nsgGenExpr`
-/

/-- `f_ε(x) = (x+ε)^p - ε^p`. -/
def nsfRegFun (p ε x : ℝ) : ℝ := (x + ε) ^ p - ε ^ p

/-- The path expression of `nsgGenExpr` for a general `C²` function (`d₁ = f'`, `d₂ = f''`): the
spectral form in the eigenvector frame of the near clock. -/
def nsfGenExpr (d₁ d₂ : ℝ → ℝ) (b E : ℝ) (q : ℝ → ℝ) (W j : ℕ) (ω : GrowthPath W) : ℝ :=
  if hA : (nearClock b E W j q ω).IsHermitian then
    nsfSpecGen (transportD0 b E) (nsgConductance (scatteringMatrix b E W j ω)) d₁ d₂
      hA.eigenvalues
      (nsgFrameDiag (scatteringMatrix b E W j ω) (hA.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ))
  else 0

/-- `nsgGenExpr` is `nsfGenExpr` at `f = f_ε`. -/
theorem nsf_nsgGenExpr_eq (b E p ε : ℝ) (q : ℝ → ℝ) (W j : ℕ) (ω : GrowthPath W) :
    nsgGenExpr b E p ε q W j ω = nsfGenExpr (nsgDeriv p ε) (nsgDeriv2 p ε) b E q W j ω := rfl

theorem nsf_eigenframe {W : ℕ} {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian) :
    ((hA.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ))ᴴ *
        (hA.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ) = 1 ∧
      A = (hA.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ) *
        diagonal (fun i => (hA.eigenvalues i : ℂ)) *
          ((hA.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ))ᴴ := by
  refine ⟨by rw [← Matrix.star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _, ?_⟩
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  rfl

/-- **The `wordDrift` identity along the path**: after the injection (`q(t) = 0`), the word generator of the clock
polynomial `Φ_π` is the spectral generator `nsfGenExpr π' π''` (eigenframe of `nsgGenExpr`).
-/
theorem nsf_polyValue_wordGenerator_path (b E : ℝ) {q : ℝ → ℝ} (hq0 : ∀ x, 0 ≤ q x)
    (W j : ℕ) (ω : GrowthPath W) (κ : Fin 0 → ℕ) (a : ℕ → ℝ) (N : ℕ) {t : ℝ} (hq : q t = 0) :
    polyValue b E κ (fun _ => q) W j ω (wordGenerator b E (fun _ => q) t (nsfClockPoly a N)) =
      ((nsfGenExpr (nsfPolyD1 a N) (nsfPolyD2 a N) b E q W j ω : ℝ) : ℂ) := by
  have hpsd := ns_nearClock_posSemidef b E W j q hq0 ω
  obtain ⟨hV, hA⟩ := nsf_eigenframe hpsd.1
  unfold nsfGenExpr
  rw [dite_eq_left hpsd.1]
  exact nsf_polyValue_wordGenerator_frame b E q W j ω κ a N t hq hV hA

/-- The value of the clock polynomial at the path: `Φ_π ↦ Σ_i π(λ_i)`. -/
theorem nsf_polyValue_clockPoly_path (b E : ℝ) {q : ℝ → ℝ} (hq0 : ∀ x, 0 ≤ q x)
    (W j : ℕ) (ω : GrowthPath W) (κ : Fin 0 → ℕ) (a : ℕ → ℝ) (N : ℕ) :
    polyValue b E κ (fun _ => q) W j ω (nsfClockPoly a N) =
      ((∑ i, nsfPolyFun a N ((ns_nearClock_posSemidef b E W j q hq0 ω).1.eigenvalues i) : ℝ) :
        ℂ) := by
  have hpsd := ns_nearClock_posSemidef b E W j q hq0 ω
  obtain ⟨hV, hA⟩ := nsf_eigenframe hpsd.1
  exact nsf_polyValue_clockPoly b E q W j ω κ a N hV hA

/-- The regularized trace `Tr f_ε(A) = Σ_i f_ε(λ_i)` (`nsClockSum nsRegKernel`, `λ_i ≥ 0`). -/
theorem nsf_clockSum_regKernel {W : ℕ} {p ε : ℝ} {A : Matrix (Fin W) (Fin W) ℂ}
    (hA : A.PosSemidef) :
    nsClockSum (nsRegKernel p ε) A = ∑ i, nsfRegFun p ε (hA.1.eigenvalues i) := by
  rw [ns_clockSum_eq _ hA.1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases (hA.eigenvalues_nonneg i).lt_or_eq with h | h
  · rw [ns_regKernel_of_pos h, nsfRegFun]
    field_simp
  · rw [← h, nsfRegFun]
    simp

end BlockBand.Endpoints
