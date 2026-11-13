module

public import BlockBand.Endpoints.Response.RemoteHigherFiniteScalar
public import BlockBand.Endpoints.Response.NearSchattenFiniteAlgebra
public import BlockBand.Endpoints.Response.RemoteHigherLimitGenerator

/-!
# The word generator of a composite clock polynomial: chain rule and bracket

For a polynomial `G` and the clock polynomial `Φ_π`, this file computes the word generator of
the composite `G(Φ_π)`: the chain rule for partial derivatives of trace polynomials
(`rhf_pderiv_aeval`, `rhf_pderiv_pderiv_aeval`), the bracket `wordCarre` on clock words in moment
form (`rhf_polyValue_wordCarre_clockPoly`) and in a unitary eigenframe (`rhfSpecBracket`), and
the evaluation `polyValue(G(Φ_π)) = G(Tr π(A))` (`rhf_polyValue_composite`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Matrix Finset Polynomial
open scoped ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

/-!
## The chain rule for the word generator
-/

section Chain

variable {nT nI : ℕ}

theorem rhf_vars_pderiv_subset (i : TraceWord nT nI) (Φ : TracePoly nT nI) :
    (MvPolynomial.pderiv i Φ).vars ⊆ Φ.vars := by
  intro v hv
  rw [MvPolynomial.mem_vars_iff_mem_support] at hv ⊢
  obtain ⟨m, hm, hvm⟩ := hv
  refine ⟨m + Finsupp.single i 1, ?_, ?_⟩
  · rw [MvPolynomial.mem_support_iff] at hm ⊢
    rw [MvPolynomial.coeff_pderiv] at hm
    exact left_ne_zero_of_mul hm
  · rw [Finsupp.mem_support_iff] at hvm ⊢
    rw [Finsupp.add_apply]
    omega

theorem rhf_pderiv_pderiv_eq_zero {Φ : TracePoly nT nI} {v : TraceWord nT nI} (hv : v ∉ Φ.vars)
    (w : TraceWord nT nI) : MvPolynomial.pderiv v (MvPolynomial.pderiv w Φ) = 0 :=
  MvPolynomial.pderiv_eq_zero_of_notMem_vars fun h => hv (rhf_vars_pderiv_subset w Φ h)

theorem rhf_sum_vars_eq {Φ : TracePoly nT nI} {S : Finset (TraceWord nT nI)} (hS : Φ.vars ⊆ S)
    (F : TraceWord nT nI → TracePoly nT nI) :
    ∑ w ∈ Φ.vars, MvPolynomial.pderiv w Φ * F w = ∑ w ∈ S, MvPolynomial.pderiv w Φ * F w :=
  Finset.sum_subset hS fun w _ hw => by
    rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars hw, zero_mul]

theorem rhf_sum_vars2_eq {Φ : TracePoly nT nI} {S : Finset (TraceWord nT nI)} (hS : Φ.vars ⊆ S)
    (F : TraceWord nT nI → TraceWord nT nI → TracePoly nT nI) :
    ∑ w ∈ Φ.vars, ∑ v ∈ Φ.vars,
        MvPolynomial.pderiv v (MvPolynomial.pderiv w Φ) * F w v =
      ∑ w ∈ S, ∑ v ∈ S, MvPolynomial.pderiv v (MvPolynomial.pderiv w Φ) * F w v := by
  rw [Finset.sum_subset hS fun w _ hw => by
    simp [MvPolynomial.pderiv_eq_zero_of_notMem_vars hw]]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_subset hS fun v _ hv => ?_
  rw [rhf_pderiv_pderiv_eq_zero hv, zero_mul]

theorem rhf_sum_carre_eq {Φ : TracePoly nT nI} {S : Finset (TraceWord nT nI)} (hS : Φ.vars ⊆ S)
    (F : TraceWord nT nI → TraceWord nT nI → TracePoly nT nI) :
    ∑ w ∈ Φ.vars, ∑ v ∈ Φ.vars,
        MvPolynomial.pderiv w Φ * MvPolynomial.pderiv v Φ * F w v =
      ∑ w ∈ S, ∑ v ∈ S, MvPolynomial.pderiv w Φ * MvPolynomial.pderiv v Φ * F w v := by
  rw [Finset.sum_subset hS fun w _ hw => by
    simp [MvPolynomial.pderiv_eq_zero_of_notMem_vars hw]]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_subset hS fun v _ hv => ?_
  rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars hv, mul_zero, zero_mul]

/-- `∂_w G(Ψ) = G'(Ψ) ∂_wΨ`. -/
theorem rhf_pderiv_aeval (Ψ : TracePoly nT nI) (G : ℝ[X]) (w : TraceWord nT nI) :
    MvPolynomial.pderiv w (aeval Ψ G) = aeval Ψ (derivative G) * MvPolynomial.pderiv w Ψ := by
  have := ((MvPolynomial.pderiv w : Derivation ℂ (TracePoly nT nI) (TracePoly nT nI)).restrictScalars
    ℝ).map_aeval G Ψ
  rw [smul_eq_mul] at this
  exact this

/-- `∂_v∂_w G(Ψ) = G''(Ψ) ∂_vΨ ∂_wΨ + G'(Ψ) ∂_v∂_wΨ`. -/
theorem rhf_pderiv_pderiv_aeval (Ψ : TracePoly nT nI) (G : ℝ[X]) (w v : TraceWord nT nI) :
    MvPolynomial.pderiv v (MvPolynomial.pderiv w (aeval Ψ G)) =
      aeval Ψ (derivative (derivative G)) * MvPolynomial.pderiv v Ψ * MvPolynomial.pderiv w Ψ +
        aeval Ψ (derivative G) * MvPolynomial.pderiv v (MvPolynomial.pderiv w Ψ) := by
  rw [rhf_pderiv_aeval, Derivation.leibniz, rhf_pderiv_aeval, smul_eq_mul, smul_eq_mul]
  ring

/-- **The chain rule for the word generator**: for every trace
polynomial `Ψ` and real polynomial `G`,
`wordGenerator(G(Ψ)) = G'(Ψ)·wordGenerator Ψ + ½ G''(Ψ)·wordCarre Ψ`.
-/
theorem rhf_wordGenerator_aeval (b E : ℝ) (q : Fin nI → ℝ → ℝ) (t : ℝ) (Ψ : TracePoly nT nI)
    (G : ℝ[X]) :
    wordGenerator b E q t (aeval Ψ G) =
      aeval Ψ (derivative G) * wordGenerator b E q t Ψ +
        MvPolynomial.C (1 / 2 : ℂ) * aeval Ψ (derivative (derivative G)) * wordCarre b E Ψ := by
  classical
  set S := (aeval Ψ G).vars ∪ Ψ.vars
  have h1 : (aeval Ψ G).vars ⊆ S := Finset.subset_union_left
  have h2 : Ψ.vars ⊆ S := Finset.subset_union_right
  unfold wordGenerator wordCarre
  rw [rhf_sum_vars_eq h1, rhf_sum_vars2_eq h1, rhf_sum_vars_eq h2, rhf_sum_vars2_eq h2,
    rhf_sum_carre_eq h2]
  simp only [rhf_pderiv_pderiv_aeval]
  simp only [rhf_pderiv_aeval]
  set G1 := aeval Ψ (derivative G)
  set G2 := aeval Ψ (derivative (derivative G))
  have hA : ∑ w ∈ S, G1 * MvPolynomial.pderiv w Ψ *
      (wordDrift (transportD0 b E) w + MvPolynomial.C (wordInjection b q t w)) =
      G1 * ∑ w ∈ S, MvPolynomial.pderiv w Ψ *
        (wordDrift (transportD0 b E) w + MvPolynomial.C (wordInjection b q t w)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by ring
  have hB : ∑ w ∈ S, ∑ v ∈ S, (G2 * MvPolynomial.pderiv v Ψ * MvPolynomial.pderiv w Ψ +
      G1 * MvPolynomial.pderiv v (MvPolynomial.pderiv w Ψ)) * wordCov (transportD0 b E) w v =
      G2 * ∑ w ∈ S, ∑ v ∈ S, MvPolynomial.pderiv w Ψ * MvPolynomial.pderiv v Ψ *
          wordCov (transportD0 b E) w v +
        G1 * ∑ w ∈ S, ∑ v ∈ S, MvPolynomial.pderiv v (MvPolynomial.pderiv w Ψ) *
          wordCov (transportD0 b E) w v := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [hA, hB]
  ring

/-- Evaluation of a composite: `polyValue(G(Ψ)) = G(polyValue Ψ)`. -/
theorem rhf_polyValue_aeval (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (W j : ℕ)
    (ω : GrowthPath W) (Ψ : TracePoly nT nI) (G : ℝ[X]) :
    polyValue b E k q W j ω (aeval Ψ G) = aeval (polyValue b E k q W j ω Ψ) G := by
  have := Polynomial.aeval_algHom_apply
    ((MvPolynomial.aeval (wordValue b E k q W j ω)).restrictScalars ℝ) Ψ G
  exact this.symm

theorem rhf_aeval_ofReal (x : ℝ) (G : ℝ[X]) : aeval (x : ℂ) G = ((G.eval x : ℝ) : ℂ) :=
  Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) x G

end Chain

/-!
## The bracket rate on clock words
-/

section Path

variable (b E : ℝ) (q : ℝ → ℝ) (W j : ℕ) (ω : GrowthPath W) (κ : Fin 0 → ℕ)

theorem rhf_prod_replicate_current_replicate (m n : ℕ) :
    ((List.replicate m nsf_x1 ++ [(TraceLetter.current, Separator.proj)] ++
        List.replicate n nsf_x1).map (nsf_lm b E q W j ω κ)).prod =
      (intervalSource b E W j q ω * nearProjection W) ^ m *
        (pathCurrent b E W j ω * nearProjection W) *
          (intervalSource b E W j q ω * nearProjection W) ^ n := by
  rw [List.map_append, List.prod_append, nsf_prod_replicate_current, nsf_prod_replicate]

theorem rhf_trace_current_middle (m n : ℕ) :
    ((intervalSource b E W j q ω * nearProjection W) ^ m *
        (pathCurrent b E W j ω * nearProjection W) *
          (intervalSource b E W j q ω * nearProjection W) ^ n).trace =
      ((intervalSource b E W j q ω * nearProjection W) ^ (n + m) *
        (pathCurrent b E W j ω * nearProjection W)).trace := by
  rw [Matrix.trace_mul_cycle, pow_add, Matrix.mul_assoc]

/-- `crossTerm` on clock words: `crossTerm((QP)^{k+1}, (QP)^{l+1}) ↦ D₀·U(k+l+2)` for every
separator pair. -/
theorem rhf_polyValue_crossTerm_clockWord (D0 : ℝ) (k l i i' : ℕ) (hi : i < k + 1)
    (hi' : i' < l + 1) :
    polyValue b E κ (fun _ => q) W j ω
        (crossTerm D0 (clockWord (k + 1)) (clockWord (l + 1)) i i') =
      ((D0 : ℝ) : ℂ) * nsfU b E q W j ω (k + l + 2) := by
  unfold crossTerm polyValue
  dsimp only
  rw [nsf_clockWord_eq, nsf_clockWord_eq, List.rotate_replicate, List.rotate_replicate,
    nsf_sepAt_replicate hi, nsf_sepAt_replicate hi', nsf_setLastSep_replicate,
    nsf_setLastSep_replicate, List.replicate_append_replicate]
  simp only [map_mul, map_add, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [nsf_wordValue_eq, nsf_wordValue_eq, nsf_wordValue_eq, nsf_prod_replicate,
    nsf_prod_replicate_current, rhf_prod_replicate_current_replicate, rhf_trace_current_middle,
    show l + 1 + (k + 1) = k + 1 + (l + 1) by omega,
    nsf_trace_QP_pow_add_current _ _ _ _ _ _ (by omega),
    show k + 1 + (l + 1) = k + l + 2 by omega]
  push_cast
  ring

/-- `wordCov` on clock words: `wordCov((QP)^{k+1}, (QP)^{l+1}) ↦ (k+1)(l+1)·D₀·U(k+l+2)`. -/
theorem rhf_polyValue_wordCov_clockWord (D0 : ℝ) (k l : ℕ) :
    polyValue b E κ (fun _ => q) W j ω (wordCov D0 (clockWord (k + 1)) (clockWord (l + 1))) =
      ((k : ℂ) + 1) * ((l : ℂ) + 1) * (((D0 : ℝ) : ℂ) * nsfU b E q W j ω (k + l + 2)) := by
  unfold wordCov
  have hk : (clockWord (k + 1)).length = k + 1 := by rw [nsf_clockWord_eq, List.length_replicate]
  have hl : (clockWord (l + 1)).length = l + 1 := by rw [nsf_clockWord_eq, List.length_replicate]
  rw [hk, hl]
  unfold polyValue
  rw [map_sum]
  simp only [map_sum]
  have hc : ∀ i ∈ range (k + 1), ∀ i' ∈ range (l + 1),
      MvPolynomial.eval (wordValue b E κ (fun _ => q) W j ω)
        (crossTerm D0 (clockWord (k + 1)) (clockWord (l + 1)) i i') =
      ((D0 : ℝ) : ℂ) * nsfU b E q W j ω (k + l + 2) := fun i hi i' hi' =>
    rhf_polyValue_crossTerm_clockWord b E q W j ω κ D0 k l i i' (Finset.mem_range.1 hi)
      (Finset.mem_range.1 hi')
  rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl (hc i hi)]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- `wordCarre` of the clock polynomial `Φ_π` in moment form:
`Σ_{r,s} a_r a_s (r+1)(s+1) D U(r+s+2)`. -/
theorem rhf_polyValue_wordCarre_clockPoly (a : ℕ → ℝ) (N : ℕ) :
    polyValue b E κ (fun _ => q) W j ω (wordCarre b E (nsfClockPoly a N)) =
      ∑ r ∈ range N, ∑ s ∈ range N, ((a r : ℝ) : ℂ) * ((a s : ℝ) : ℂ) *
        (((r : ℂ) + 1) * ((s : ℂ) + 1) *
          (((transportD0 b E : ℝ) : ℂ) * nsfU b E q W j ω (r + s + 2))) := by
  unfold wordCarre
  have e1 : ∀ w ∈ (nsfClockPoly a N).vars, ∑ v ∈ (nsfClockPoly a N).vars,
      MvPolynomial.pderiv w (nsfClockPoly a N) * MvPolynomial.pderiv v (nsfClockPoly a N) *
        wordCov (transportD0 b E) w v =
      ∑ s ∈ range N, MvPolynomial.C ((a s : ℝ) : ℂ) *
        (MvPolynomial.pderiv w (nsfClockPoly a N) *
          wordCov (transportD0 b E) w (clockWord (s + 1))) := by
    intro w _
    rw [← nsf_sum_vars_pderiv_mul a N (fun v => MvPolynomial.pderiv w (nsfClockPoly a N) *
      wordCov (transportD0 b E) w v)]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [Finset.sum_congr rfl e1]
  have e2 : ∀ w ∈ (nsfClockPoly a N).vars, ∑ s ∈ range N, MvPolynomial.C ((a s : ℝ) : ℂ) *
      (MvPolynomial.pderiv w (nsfClockPoly a N) *
        wordCov (transportD0 b E) w (clockWord (s + 1))) =
      MvPolynomial.pderiv w (nsfClockPoly a N) * ∑ s ∈ range N, MvPolynomial.C ((a s : ℝ) : ℂ) *
        wordCov (transportD0 b E) w (clockWord (s + 1)) := by
    intro w _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  rw [Finset.sum_congr rfl e2, nsf_sum_vars_pderiv_mul a N (fun w => ∑ s ∈ range N,
    MvPolynomial.C ((a s : ℝ) : ℂ) * wordCov (transportD0 b E) w (clockWord (s + 1)))]
  unfold polyValue
  rw [map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_mul, map_sum, MvPolynomial.eval_C, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul, MvPolynomial.eval_C]
  have := rhf_polyValue_wordCov_clockWord b E q W j ω κ (transportD0 b E) r s
  unfold polyValue at this
  rw [this]
  ring

end Path

/-!
## The bracket in a unitary eigenframe
-/

/-- The spectral bracket `D Σ_i (λ_i d₁(λ_i))² s_i` of a function with derivative `d₁`. -/
def rhfSpecBracket {ι : Type*} [Fintype ι] (D : ℝ) (d₁ : ℝ → ℝ) (lam s : ι → ℝ) : ℝ :=
  D * ∑ i, (lam i * d₁ (lam i)) ^ 2 * s i

theorem rhf_rhlSpecBracket_eq {ι : Type*} [Fintype ι] (D p ε : ℝ) (lam s : ι → ℝ) :
    rhlSpecBracket D p ε lam s = rhfSpecBracket D (nsgDeriv p ε) lam s := rfl

/-- The polynomial bracket in moment form. -/
theorem rhf_specBracket_poly {ι : Type*} [Fintype ι] (D : ℝ) (a : ℕ → ℝ) (N : ℕ)
    (lam s : ι → ℝ) :
    rhfSpecBracket D (nsfPolyD1 a N) lam s =
      ∑ r ∈ range N, ∑ t ∈ range N, a r * a t * (((r : ℝ) + 1) * ((t : ℝ) + 1) *
        (D * ∑ i, lam i ^ (r + t + 2) * s i)) := by
  unfold rhfSpecBracket nsfPolyD1
  have e : ∀ i, (lam i * ∑ r ∈ range N, a r * ((r : ℝ) + 1) * lam i ^ r) ^ 2 * s i =
      ∑ r ∈ range N, ∑ t ∈ range N, a r * a t * (((r : ℝ) + 1) * ((t : ℝ) + 1) *
        (lam i ^ (r + t + 2) * s i)) := by
    intro i
    rw [Finset.mul_sum, sq, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [show r + t + 2 = (r + 1) + (t + 1) by omega, pow_add]
    ring
  simp only [e]
  simp only [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **`wordCarre` of a clock polynomial in a unitary eigenframe**:
`wordCarre Φ_π ↦ D Σ_i (λ_i π'(λ_i))² S^V_ii`.
-/
theorem rhf_polyValue_wordCarre_frame (b E : ℝ) (q : ℝ → ℝ) (W j : ℕ) (ω : GrowthPath W)
    (κ : Fin 0 → ℕ) (a : ℕ → ℝ) (N : ℕ) {V : Matrix (Fin W) (Fin W) ℂ} (hV : Vᴴ * V = 1)
    {lam : Fin W → ℝ}
    (hA : nearClock b E W j q ω = V * diagonal (fun i => (lam i : ℂ)) * Vᴴ) :
    polyValue b E κ (fun _ => q) W j ω (wordCarre b E (nsfClockPoly a N)) =
      ((rhfSpecBracket (transportD0 b E) (nsfPolyD1 a N) lam
        (nsgFrameDiag (scatteringMatrix b E W j ω) V) : ℝ) : ℂ) := by
  rw [rhf_polyValue_wordCarre_clockPoly, rhf_specBracket_poly]
  simp only [nsf_U_frame b E q W j ω hV hA]
  push_cast
  rfl

/-- The bracket at the path of length `j` for a function with derivative `d₁` (same frame and
data as `rhlBracketExpr`). -/
def rhfBracketExpr (d₁ : ℝ → ℝ) (b E : ℝ) (q : ℝ → ℝ) (W j : ℕ) (ω : GrowthPath W) : ℝ :=
  if hA : (nearClock b E W j q ω).IsHermitian then
    rhfSpecBracket (transportD0 b E) d₁ hA.eigenvalues
      (nsgFrameDiag (scatteringMatrix b E W j ω) (hA.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ))
  else 0

theorem rhf_rhlBracketExpr_eq (b E p ε : ℝ) (q : ℝ → ℝ) (W j : ℕ) (ω : GrowthPath W) :
    rhlBracketExpr b E p ε q W j ω = rhfBracketExpr (nsgDeriv p ε) b E q W j ω := rfl

theorem rhf_polyValue_wordCarre_path (b E : ℝ) {q : ℝ → ℝ} (hq0 : ∀ x, 0 ≤ q x) (W j : ℕ)
    (ω : GrowthPath W) (κ : Fin 0 → ℕ) (a : ℕ → ℝ) (N : ℕ) :
    polyValue b E κ (fun _ => q) W j ω (wordCarre b E (nsfClockPoly a N)) =
      ((rhfBracketExpr (nsfPolyD1 a N) b E q W j ω : ℝ) : ℂ) := by
  have hpsd := ns_nearClock_posSemidef b E W j q hq0 ω
  obtain ⟨hV, hA⟩ := nsf_eigenframe hpsd.1
  unfold rhfBracketExpr
  rw [dite_eq_left hpsd.1]
  exact rhf_polyValue_wordCarre_frame b E q W j ω κ a N hV hA

/-!
## The composite clock polynomial
-/

/-- `G(Φ_π)`, `Φ_π = Σ_{r<N} a_r Tr(QP)^{r+1}`, an ordinary trace polynomial of the one-source
family. -/
def rhfComposite (a : ℕ → ℝ) (N : ℕ) (G : ℝ[X]) : TracePoly 0 1 := aeval (nsfClockPoly a N) G

theorem rhf_isOrdinaryPoly_composite (a : ℕ → ℝ) (N : ℕ) (G : ℝ[X]) :
    IsOrdinaryPoly (rhfComposite a N G) := by
  intro w hw
  refine nsf_isOrdinaryPoly_clockPoly a N w ?_
  -- a variable of `G(Ψ)` is a variable of some `Ψ^k`, hence of `Ψ`
  have hsub : (rhfComposite a N G).vars ⊆ (nsfClockPoly a N).vars := by
    unfold rhfComposite
    rw [aeval_eq_sum_range]
    refine (MvPolynomial.vars_sum_subset _ _).trans (Finset.biUnion_subset.2 fun n _ => ?_)
    rw [Algebra.smul_def, MvPolynomial.algebraMap_apply]
    refine (MvPolynomial.vars_mul _ _).trans (Finset.union_subset ?_ (MvPolynomial.vars_pow _ _))
    rw [MvPolynomial.vars_C]
    exact Finset.empty_subset _
  exact hsub hw

/-- The real value `Tr π(A)` of the clock polynomial at the path. -/
def rhfClockVal (b E : ℝ) (q : ℝ → ℝ) (a : ℕ → ℝ) (N W j : ℕ) (ω : GrowthPath W) : ℝ :=
  (polyValue b E (noTags W) (fun _ => q) W j ω (nsfClockPoly a N)).re

theorem rhf_polyValue_clockPoly_ofReal (b E : ℝ) {q : ℝ → ℝ} (hq0 : ∀ x, 0 ≤ q x)
    (a : ℕ → ℝ) (N W j : ℕ) (ω : GrowthPath W) :
    polyValue b E (noTags W) (fun _ => q) W j ω (nsfClockPoly a N) =
      ((rhfClockVal b E q a N W j ω : ℝ) : ℂ) := by
  unfold rhfClockVal
  rw [nsf_polyValue_clockPoly_path b E hq0 W j ω (noTags W) a N, Complex.ofReal_re]

/-- The value of the composite: `polyValue(G(Φ_π)) = G(Tr π(A))`. -/
theorem rhf_polyValue_composite (b E : ℝ) {q : ℝ → ℝ} (hq0 : ∀ x, 0 ≤ q x) (a : ℕ → ℝ)
    (N W j : ℕ) (ω : GrowthPath W) (G : ℝ[X]) :
    polyValue b E (noTags W) (fun _ => q) W j ω (rhfComposite a N G) =
      ((G.eval (rhfClockVal b E q a N W j ω) : ℝ) : ℂ) := by
  rw [rhfComposite, rhf_polyValue_aeval, rhf_polyValue_clockPoly_ofReal b E hq0, rhf_aeval_ofReal]

/-- **The word generator of the composite at the path** after the injection
(`q(t) = 0`):
`G'(Tr π(A))·𝒢_π + ½ G''(Tr π(A))·Γ_π`.
-/
theorem rhf_polyValue_wordGenerator_composite_path (b E : ℝ) {q : ℝ → ℝ} (hq0 : ∀ x, 0 ≤ q x)
    (a : ℕ → ℝ) (N W j : ℕ) (ω : GrowthPath W) (G : ℝ[X]) {t : ℝ} (hqt : q t = 0) :
    polyValue b E (noTags W) (fun _ => q) W j ω
        (wordGenerator b E (fun _ => q) t (rhfComposite a N G)) =
      ((((derivative G).eval (rhfClockVal b E q a N W j ω)) *
          nsfGenExpr (nsfPolyD1 a N) (nsfPolyD2 a N) b E q W j ω +
        1 / 2 * ((derivative (derivative G)).eval (rhfClockVal b E q a N W j ω)) *
          rhfBracketExpr (nsfPolyD1 a N) b E q W j ω : ℝ) : ℂ) := by
  rw [rhfComposite, rhf_wordGenerator_aeval]
  unfold polyValue
  simp only [map_add, map_mul, MvPolynomial.eval_C]
  have h1 := rhf_polyValue_aeval b E (noTags W) (fun _ => q) W j ω (nsfClockPoly a N)
    (derivative G)
  have h2 := rhf_polyValue_aeval b E (noTags W) (fun _ => q) W j ω (nsfClockPoly a N)
    (derivative (derivative G))
  have h3 := nsf_polyValue_wordGenerator_path b E hq0 W j ω (noTags W) a N hqt
  have h4 := rhf_polyValue_wordCarre_path b E hq0 W j ω (noTags W) a N
  have h5 := rhf_polyValue_clockPoly_ofReal b E hq0 a N W j ω
  unfold polyValue at h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4, h5, rhf_aeval_ofReal, rhf_aeval_ofReal]
  push_cast
  ring

end BlockBand.Endpoints
